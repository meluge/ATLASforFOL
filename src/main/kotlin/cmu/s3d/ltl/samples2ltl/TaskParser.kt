package cmu.s3d.fol.samples2fol

import cmu.s3d.fol.*
import cmu.s3d.fol.learning.FOLLearner
import cmu.s3d.fol.learning.FOLTask
import edu.mit.csail.sdg.translator.A4Options
import kotlinx.serialization.*
import kotlinx.serialization.json.*

// Data classes for JSON format
@Serializable
data class JsonFOLTask(
    val sorts: List<String>,
    val relations: List<JsonRelation>,
    val functions: List<JsonFunction> = emptyList(),
    val positiveExamples: List<JsonExample>,
    val negativeExamples: List<JsonExample>,
    val maxNodes: Int = 10
)

@Serializable
data class JsonRelation(
    val name: String,
    val signature: List<String>
)

@Serializable
data class JsonFunction(
    val name: String,
    val signature: List<String>
)

@Serializable
data class JsonExample(
    val constants: List<JsonConstant>,
    val relationFacts: Map<String, List<List<String>>> = emptyMap(),
    val functionFacts: Map<String, List<List<String>>> = emptyMap()
)

@Serializable
data class JsonConstant(
    val name: String,
    val sort: String
)

sealed class SExpr {
    data class Atom(val value: String) : SExpr()
    data class List(val elements: kotlin.collections.List<SExpr>) : SExpr()
}

object FOLTaskParser {

    fun parseTask(taskString: String, filename: String = ""): FOLTask {
        return when {
            filename.endsWith(".json") || taskString.trim().startsWith("{") -> {
                parseJsonFormat(taskString)
            }
            else -> {
                parseFolFormat(taskString)
            }
        }
    }

    private fun parseJsonFormat(jsonString: String): FOLTask {
        val jsonTask = Json.decodeFromString<JsonFOLTask>(jsonString)

        return FOLTask(
            sorts = jsonTask.sorts.map { FOLSort(it) },
            relations = jsonTask.relations.map { FOLRelation(it.name, it.signature) },
            functions = jsonTask.functions.map { FOLFunction(it.name, it.signature) },
            positiveExamples = jsonTask.positiveExamples.map {
                FOLExample(
                    structure = FOLStructure(
                        constants = it.constants.map { c -> FOLConstant(c.name, c.sort) },
                        relationFacts = it.relationFacts,
                        functionFacts = it.functionFacts
                    ),
                    isPositive = true
                )
            },
            negativeExamples = jsonTask.negativeExamples.map {
                FOLExample(
                    structure = FOLStructure(
                        constants = it.constants.map { c -> FOLConstant(c.name, c.sort) },
                        relationFacts = it.relationFacts,
                        functionFacts = it.functionFacts
                    ),
                    isPositive = false
                )
            },
            maxNumOfNode = jsonTask.maxNodes
        )
    }

    private fun parseFolFormat(taskString: String): FOLTask {
        val sexprs = parseSExpressions(taskString)

        val sorts = mutableListOf<FOLSort>()
        val relations = mutableListOf<FOLRelation>()
        val functions = mutableListOf<FOLFunction>()
        val positiveExamples = mutableListOf<FOLExample>()
        val negativeExamples = mutableListOf<FOLExample>()

        for (sexpr in sexprs) {
            when (sexpr) {
                is SExpr.List -> {
                    if (sexpr.elements.isNotEmpty()) {
                        val head = (sexpr.elements[0] as? SExpr.Atom)?.value
                        when (head) {
                            "sort" -> {
                                if (sexpr.elements.size >= 2) {
                                    val sortName = (sexpr.elements[1] as? SExpr.Atom)?.value
                                    if (sortName != null) {
                                        sorts.add(FOLSort(sortName))
                                    }
                                }
                            }
                            "relation" -> {
                                if (sexpr.elements.size >= 3) {
                                    val relName = (sexpr.elements[1] as? SExpr.Atom)?.value
                                    val signature = sexpr.elements.drop(2).mapNotNull { (it as? SExpr.Atom)?.value }
                                    if (relName != null) {
                                        relations.add(FOLRelation(relName, signature))
                                    }
                                }
                            }
                            "function" -> {
                                if (sexpr.elements.size >= 3) {
                                    val funcName = (sexpr.elements[1] as? SExpr.Atom)?.value
                                    val signature = sexpr.elements.drop(2).mapNotNull { (it as? SExpr.Atom)?.value }
                                    if (funcName != null) {
                                        functions.add(FOLFunction(funcName, signature))
                                    }
                                }
                            }
                            "model" -> {
                                if (sexpr.elements.size >= 3) {
                                    val polarity = (sexpr.elements[1] as? SExpr.Atom)?.value
                                    val isPositive = polarity == "+"
                                    val example = parseModelContents(sexpr.elements.drop(2))
                                    if (isPositive) {
                                        positiveExamples.add(FOLExample(example, true))
                                    } else {
                                        negativeExamples.add(FOLExample(example, false))
                                    }
                                }
                            }
                        }
                    }
                }
                else -> continue
            }
        }

        return FOLTask(
            sorts = sorts,
            relations = relations,
            functions = functions,
            positiveExamples = positiveExamples,
            negativeExamples = negativeExamples,
            maxNumOfNode = 8
        )
    }

    private fun parseModelContents(elements: List<SExpr>): FOLStructure {
        val constants = mutableListOf<FOLConstant>()
        val relationFacts = mutableMapOf<String, MutableList<List<String>>>()
        val functionFacts = mutableMapOf<String, MutableList<List<String>>>()

        for (element in elements) {
            when (element) {
                is SExpr.List -> {
                    if (element.elements.isNotEmpty()) {
                        if (element.elements.all { it is SExpr.List && (it as SExpr.List).elements.size == 2 }) {
                            for (constExpr in element.elements) {
                                val constList = constExpr as SExpr.List
                                val constName = (constList.elements[0] as? SExpr.Atom)?.value
                                val constSort = (constList.elements[1] as? SExpr.Atom)?.value
                                if (constName != null && constSort != null) {
                                    constants.add(FOLConstant(constName, constSort))
                                }
                            }
                        } else {
                            val head = (element.elements[0] as? SExpr.Atom)?.value
                            when (head) {
                                "=" -> {
                                    if (element.elements.size == 3 && element.elements[1] is SExpr.List) {
                                        val funcCall = element.elements[1] as SExpr.List
                                        val result = (element.elements[2] as? SExpr.Atom)?.value
                                        if (funcCall.elements.isNotEmpty() && result != null) {
                                            val funcName = (funcCall.elements[0] as? SExpr.Atom)?.value
                                            val args = funcCall.elements.drop(1).mapNotNull { (it as? SExpr.Atom)?.value }
                                            if (funcName != null) {
                                                functionFacts.getOrPut(funcName) { mutableListOf() }.add(args + result)
                                            }
                                        }
                                    }
                                }
                                else -> {
                                    if (head != null) {
                                        val args = element.elements.drop(1).mapNotNull { (it as? SExpr.Atom)?.value }
                                        relationFacts.getOrPut(head) { mutableListOf() }.add(args)
                                    }
                                }
                            }
                        }
                    }
                }
                else -> continue
            }
        }

        return FOLStructure(
            constants = constants,
            relationFacts = relationFacts.mapValues { it.value.toList() },
            functionFacts = functionFacts.mapValues { it.value.toList() }
        )
    }

    private fun parseSExpressions(input: String): List<SExpr> {
        val tokens = tokenize(input)
        val result = mutableListOf<SExpr>()
        var index = 0

        while (index < tokens.size) {
            val (expr, newIndex) = parseExpression(tokens, index)
            result.add(expr)
            index = newIndex
        }

        return result
    }

    private fun tokenize(input: String): List<String> {
        val tokens = mutableListOf<String>()
        var i = 0

        while (i < input.length) {
            when {
                input[i].isWhitespace() -> i++
                input[i] == ';' -> {
                    // Skip comment line
                    while (i < input.length && input[i] != '\n') i++
                }
                input[i] == '(' -> {
                    tokens.add("(")
                    i++
                }
                input[i] == ')' -> {
                    tokens.add(")")
                    i++
                }
                else -> {
                    // Read atom
                    val start = i
                    while (i < input.length && !input[i].isWhitespace() && input[i] != '(' && input[i] != ')') {
                        i++
                    }
                    tokens.add(input.substring(start, i))
                }
            }
        }

        return tokens
    }

    private fun parseExpression(tokens: List<String>, startIndex: Int): Pair<SExpr, Int> {
        if (startIndex >= tokens.size) {
            throw IllegalArgumentException("Unexpected end of input")
        }

        return when (tokens[startIndex]) {
            "(" -> {
                val elements = mutableListOf<SExpr>()
                var index = startIndex + 1

                while (index < tokens.size && tokens[index] != ")") {
                    val (expr, newIndex) = parseExpression(tokens, index)
                    elements.add(expr)
                    index = newIndex
                }

                if (index >= tokens.size) {
                    throw IllegalArgumentException("Unmatched opening parenthesis")
                }

                Pair(SExpr.List(elements), index + 1)
            }
            ")" -> {
                throw IllegalArgumentException("Unexpected closing parenthesis")
            }
            else -> {
                Pair(SExpr.Atom(tokens[startIndex]), startIndex + 1)
            }
        }
    }
}

fun FOLTask.buildLearner(options: A4Options? = null, minimized: Boolean = true): FOLLearner {
    return FOLLearner(
        task = this,
        customAlloyOptions = options,
        minimized = minimized
    )
}

fun FOLTask.toCSVString(): String {
    return "${positiveExamples.size},${negativeExamples.size},${maxNumOfNode},${sorts.size},${relations.size}"
}