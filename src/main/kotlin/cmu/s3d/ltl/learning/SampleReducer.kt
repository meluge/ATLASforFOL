package cmu.s3d.fol.learning

import cmu.s3d.fol.*

class SampleReducer(
    private val positiveExamples: List<FOLExample>,
    private val negativeExamples: List<FOLExample>
) {

    fun reduceSamples(): Pair<List<FOLExample>, List<FOLExample>> {
        val reducedPositives = positiveExamples.map { reduceExample(it) }
        val reducedNegatives = negativeExamples.map { reduceExample(it) }
        return Pair(reducedPositives, reducedNegatives)
    }

    private fun reduceExample(example: FOLExample): FOLExample {
        val reducedStructure = reduceStructure(example.structure)
        return FOLExample(reducedStructure, example.isPositive)
    }

    private fun reduceStructure(structure: FOLStructure): FOLStructure {
        val constantMapping = createCanonicalConstantMapping(structure.constants)

        val reducedConstants = reduceConstants(structure.constants, constantMapping)

        val reducedRelationFacts = reduceRelationFacts(structure.relationFacts, constantMapping)

        val reducedFunctionFacts = reduceFunctionFacts(structure.functionFacts, constantMapping)

        return FOLStructure(
            constants = reducedConstants,
            relationFacts = reducedRelationFacts,
            functionFacts = reducedFunctionFacts
        )
    }

    private fun createCanonicalConstantMapping(constants: List<FOLConstant>): Map<String, String> {
        val mapping = mutableMapOf<String, String>()
        val sortCounters = mutableMapOf<String, Int>()

        // Group constants by sort and create canonical names
        constants.groupBy { it.sort }.forEach { (sort, constantsOfSort) ->
            constantsOfSort.forEachIndexed { index, constant ->
                val canonicalName = "${sort.lowercase()}$index"
                mapping[constant.name] = canonicalName
                sortCounters[sort] = index + 1
            }
        }

        return mapping
    }

    private fun reduceConstants(
        constants: List<FOLConstant>,
        mapping: Map<String, String>
    ): List<FOLConstant> {
        return constants.map { constant ->
            FOLConstant(
                name = mapping[constant.name] ?: constant.name,
                sort = constant.sort
            )
        }.distinctBy { "${it.name}_${it.sort}" } // Remove duplicates
    }

    private fun reduceRelationFacts(
        relationFacts: Map<String, List<List<String>>>,
        constantMapping: Map<String, String>
    ): Map<String, List<List<String>>> {
        return relationFacts.mapValues { (_, facts) ->
            facts.map { fact ->
                fact.map { constantName ->
                    constantMapping[constantName] ?: constantName
                }
            }.distinct() // Remove duplicate facts
        }
    }

    private fun reduceFunctionFacts(
        functionFacts: Map<String, List<List<String>>>,
        constantMapping: Map<String, String>
    ): Map<String, List<List<String>>> {
        // Since we're converting functions to relations, this should handle empty maps
        if (functionFacts.isEmpty()) return emptyMap()

        return functionFacts.mapValues { (_, facts) ->
            facts.map { fact ->
                fact.map { constantName ->
                    constantMapping[constantName] ?: constantName
                }
            }.distinct()
        }
    }


    fun areEquivalent(example1: FOLExample, example2: FOLExample): Boolean {
        if (example1.isPositive != example2.isPositive) return false

        val reduced1 = reduceExample(example1)
        val reduced2 = reduceExample(example2)

        return structuresAreEquivalent(reduced1.structure, reduced2.structure)
    }

    private fun structuresAreEquivalent(struct1: FOLStructure, struct2: FOLStructure): Boolean {
        val sorts1 = struct1.constants.groupBy { it.sort }.mapValues { it.value.size }
        val sorts2 = struct2.constants.groupBy { it.sort }.mapValues { it.value.size }
        if (sorts1 != sorts2) return false

        if (struct1.relationFacts.keys != struct2.relationFacts.keys) return false
        for (relationName in struct1.relationFacts.keys) {
            val facts1 = struct1.relationFacts[relationName]?.toSet() ?: emptySet()
            val facts2 = struct2.relationFacts[relationName]?.toSet() ?: emptySet()
            if (facts1 != facts2) return false
        }

        if (struct1.functionFacts.keys != struct2.functionFacts.keys) return false
        for (functionName in struct1.functionFacts.keys) {
            val facts1 = struct1.functionFacts[functionName]?.toSet() ?: emptySet()
            val facts2 = struct2.functionFacts[functionName]?.toSet() ?: emptySet()
            if (facts1 != facts2) return false
        }

        return true
    }


    fun removeRedundantExamples(): Pair<List<FOLExample>, List<FOLExample>> {
        val reducedPositives = mutableListOf<FOLExample>()
        val reducedNegatives = mutableListOf<FOLExample>()

        for (example in positiveExamples) {
            val reduced = reduceExample(example)
            if (reducedPositives.none { areEquivalent(it, reduced) }) {
                reducedPositives.add(reduced)
            }
        }

        for (example in negativeExamples) {
            val reduced = reduceExample(example)
            if (reducedNegatives.none { areEquivalent(it, reduced) }) {
                reducedNegatives.add(reduced)
            }
        }

        return Pair(reducedPositives, reducedNegatives)
    }


    fun getReductionStats(): ReductionStats {
        val (reducedPos, reducedNeg) = removeRedundantExamples()

        return ReductionStats(
            originalPositiveCount = positiveExamples.size,
            originalNegativeCount = negativeExamples.size,
            reducedPositiveCount = reducedPos.size,
            reducedNegativeCount = reducedNeg.size,
            totalReduction = (positiveExamples.size + negativeExamples.size) - (reducedPos.size + reducedNeg.size)
        )
    }
}

data class ReductionStats(
    val originalPositiveCount: Int,
    val originalNegativeCount: Int,
    val reducedPositiveCount: Int,
    val reducedNegativeCount: Int,
    val totalReduction: Int
) {
    val reductionPercentage: Double
        get() = if (originalPositiveCount + originalNegativeCount > 0) {
            (totalReduction.toDouble() / (originalPositiveCount + originalNegativeCount)) * 100
        } else 0.0
}