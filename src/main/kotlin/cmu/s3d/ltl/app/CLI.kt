package cmu.s3d.fol.app

import cmu.s3d.fol.learning.AlloyMaxBase
import cmu.s3d.fol.samples2fol.FOLTaskParser
import cmu.s3d.fol.samples2fol.buildLearner
import cmu.s3d.fol.samples2fol.toCSVString
import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.int
import edu.mit.csail.sdg.translator.A4Options
import java.io.File
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

class CLI : CliktCommand(
    name = "FOL-Atlas",
    help = "A tool to learn FOL formulas from positive and negative examples using AlloyMax."
) {
    private val solver by option("--solver", "-s", help = "The AlloyMax solver to use. Default: SAT4JMax").default("SAT4JMax")
    private val filename by option("--filename", "-f", help = "The file containing one task to run.")
    private val traces by option("--traces", "-t", help = "The folder containing the tasks to run. It will find all task files under the folder recursively.")
    private val timeout by option("--timeout", "-T", help = "The timeout in seconds for solving each task.").int().default(0)
    private val model by option("--model", "-m", help = "Print the model to use for learning.").flag(default = false)
    private val findAny by option("--findAny", "-A", help = "Find any solution. Default: false").flag(default = false)

    override fun run() {
        if (filename == null && traces == null) {
            println("Please provide a filename or a folder with traces.")
            return
        }

        println("filename,numOfPositives,numOfNegatives,maxNumOfOP,numOfSorts,numOfRelations,solvingTime,formula")

        if (filename != null) {
            val f = File(filename!!)
            if (f.isFile && (f.name.endsWith(".fol") || f.name.endsWith(".json"))) {
                runLearningTask(f, filename!!)
            } else {
                error("The file $filename does not exist or is not a .fol/.json file.")
            }
        } else if (traces != null) {
            val folder = File(traces!!)
            if (folder.isDirectory) {
                folder.walk()
                    .filter { it.isFile && (it.name.endsWith(".fol") || it.name.endsWith(".json")) }
                    .forEach { runLearningTask(it, it.path) }
            }
        }
    }

    private fun runLearningTask(f: File, pathName: String) {
        val options = AlloyMaxBase.defaultAlloyOptions()
        options.solver = when (solver) {
            "SAT4JMax" -> A4Options.SatSolver.SAT4JMax
            "OpenWBO" -> A4Options.SatSolver.OpenWBO
            else -> A4Options.SatSolver.SAT4JMax
        }

        val task = FOLTaskParser.parseTask(f.readText(), f.name)

        // Add debug output
        println("Parsed task: ${task.sorts.size} sorts, ${task.relations.size} relations")
        println("Positive examples: ${task.positiveExamples.size}")
        println("Negative examples: ${task.negativeExamples.size}")
        println("Max nodes: ${task.maxNumOfNode}")

        val learner = task.buildLearner(options, !findAny)
        if (model) {
            println(learner.generateAlloyModel(8).trimIndent())
            return  // Exit early if just printing model
        }

        val executor = Executors.newSingleThreadExecutor()
        val future = executor.submit {
            val startTime = System.currentTimeMillis()
            println("Starting learning process...")
            val solution = learner.learn()
            val solvingTime = (System.currentTimeMillis() - startTime).toDouble() / 1000

            if (solution != null) {
                println(solution.debugFormulaStructure())
                println("Solution found!")
                val formula = solution.getFOL2()
                println("Formula: $formula")
                println("$pathName,${task.toCSVString()},$solvingTime,\"$formula\"")
            } else {
                println("No solution found (UNSAT)")
                println("$pathName,${task.toCSVString()},$solvingTime,UNSAT")
            }
        }

    }
}

fun main(args: Array<String>) {
    CLI().main(args)
}