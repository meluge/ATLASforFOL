package cmu.s3d.ltl.samples2ltl

import cmu.s3d.ltl.LassoTrace
import cmu.s3d.ltl.State
import cmu.s3d.ltl.learning.LTLLearner
import kotlin.math.pow

data class Task(
    val learner: LTLLearner,
    val numOfPositives: Int,
    val numOfNegatives: Int,
    val depth: Int,
    val numOfVariables: Int,
    val maxLengthOfTraces: Int,
    val expected: String?
)

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
        "props" to "props"
    )

    fun parseTask(task: String): Task {
        val parts = task.split("---")
        val positives = parts[0].trim()
        val negatives = parts[1].trim()
        val operators = parts[2].trim()
        val depth = parts[3].trim().toInt()
        val expected = if (parts.size > 4) parts[4].trim() else null

        val literals = positives.split(";")[0].split(",").indices.map { "x$it" }
        val positiveExamples = parseExamples(positives)
        val negativeExamples = parseExamples(negatives)

        return Task(
            learner = LTLLearner(
                literals = literals,
                positiveExamples = positiveExamples,
                negativeExamples = negativeExamples,
                maxNumOfNode = (2.0).pow(depth).toInt() - 1 + literals.size,
                excludedOperators = parseExcludedOperators(operators)
            ),
            numOfPositives = positiveExamples.size,
            numOfNegatives = negativeExamples.size,
            depth = depth,
            numOfVariables = literals.size,
            maxLengthOfTraces = (positiveExamples + negativeExamples).maxOf { it.length() },
            expected = expected
        )
    }

    private fun parseExamples(examples: String): List<LassoTrace> {
        return examples.lines().map {
            val line = it.trim()
            val parts = line.split("::")
            val trace = parseTrace(parts[0])
            val lasso = parts[1].toInt()
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