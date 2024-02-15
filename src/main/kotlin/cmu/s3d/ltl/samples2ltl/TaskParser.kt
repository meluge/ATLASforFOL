package cmu.s3d.ltl.samples2ltl

import cmu.s3d.ltl.LassoTrace
import cmu.s3d.ltl.State
import cmu.s3d.ltl.learning.LTLLearner
import edu.mit.csail.sdg.translator.A4Options
import kotlin.math.pow

data class Task(
    val literals: List<String>,
    val positiveExamples: List<LassoTrace>,
    val negativeExamples: List<LassoTrace>,
    val excludedOperators: List<String>,
    val depth: Int,
    val expected: String?,
    val customConstraints: String?
) {
    fun buildLearner(options: A4Options? = null): LTLLearner {
        return LTLLearner(
            literals = literals,
            positiveExamples = positiveExamples,
            negativeExamples = negativeExamples,
            maxNumOfNode = (2.0).pow(depth).toInt() - 1 + literals.size,
            excludedOperators = excludedOperators,
            customAlloyOptions = options,
            customConstraints = customConstraints?.let { "\n${it.prependIndent("            ")}\n" } ?: ""
        )
    }

    fun numOfPositives(): Int {
        return positiveExamples.size
    }

    fun numOfNegatives(): Int {
        return negativeExamples.size
    }

    fun numOfVariables(): Int {
        return literals.size
    }

    fun maxLengthOfTraces(): Int {
        return (positiveExamples + negativeExamples).maxOf { it.length() }
    }

    fun toCSVString(): String {
        return "${numOfPositives()},${numOfNegatives()},$depth,${numOfVariables()},${maxLengthOfTraces()},\"$expected\""
    }
}

object TaskParser {

    private val operatorMapping = mapOf(
        "G"  to "G",
        "F"  to "F",
        "!"  to "Neg",
        "U"  to "Until",
        "&"  to "And",
        "|"  to "Or",
        "->" to "Imply",
        "X"  to "X",
        "prop" to "prop"
    )

    fun parseTask(task: String): Task {
        val parts = task.split("---")
        val positives = parts[0].trim()
        val negatives = parts[1].trim()
        val operators = parts[2].trim()
        val depth = parts[3].trim().toInt()
        val expected = if (parts.size > 4) parts[4].trim() else null
        val constraints = if (parts.size > 5) parts[5].trim() else null

        val positiveExamples = parseExamples(positives)
        val negativeExamples = parseExamples(negatives)
        val numOfLiterals = let {
            if (positiveExamples.isEmpty())
                negativeExamples.first()
            else
                positiveExamples.first()
        }.getStateAt(0).values.size
        val literals = (0 until numOfLiterals).map { "x$it" }
        return Task(
            literals = literals,
            positiveExamples = positiveExamples,
            negativeExamples = negativeExamples,
            excludedOperators = parseExcludedOperators(operators),
            depth = depth,
            expected = expected,
            customConstraints = constraints
        )
    }

    private fun parseExamples(examples: String): List<LassoTrace> {
        return if (examples.isBlank())
            emptyList()
        else
            examples.lines().map {
                val line = it.trim()
                val parts = line.split("::")
                val trace = parseTrace(parts[0])
                val lasso = if (parts.size == 1 || parts[1].isBlank())
                    0
                else if (parts[1][0] == '[')
                    parts[1].substring(1, parts[1].length-1).toInt()
                else
                    parts[1].toInt()
                LassoTrace(prefix = trace.subList(0, lasso), loop = trace.subList(lasso, trace.size))
            }
    }

    private fun parseExcludedOperators(operators: String): List<String> {
        val ops = operators.split(",").map { operatorMapping[it.trim()]!! }
        return operatorMapping.values - ops.toSet()
    }

    private fun parseTrace(trace: String): List<State> {
        val states = trace.split(";")
        return states.map { s ->
            val values = s.split(",")
            State(values.indices.associate { "x$it" to (values[it].trim() == "1") })
        }
    }
}