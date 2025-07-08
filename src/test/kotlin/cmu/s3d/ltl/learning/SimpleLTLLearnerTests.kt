package cmu.s3d.fol.learning

import cmu.s3d.fol.*
import cmu.s3d.fol.learning.FOLLearner
import cmu.s3d.fol.learning.FOLTask
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class SimpleFOLLearnerTests {
    @Test
    fun testSimpleForall() {
        val task = FOLTask(
            sorts = listOf(FOLSort("Node")),
            relations = listOf(FOLRelation("edge", listOf("Node", "Node"))),
            functions = emptyList(),
            positiveExamples = listOf(
                FOLExample(
                    structure = FOLStructure(
                        constants = listOf(
                            FOLConstant("a", "Node"),
                            FOLConstant("b", "Node")
                        ),
                        relationFacts = mapOf(
                            "edge" to listOf(
                                listOf("a", "b"),
                                listOf("b", "a")
                            )
                        )
                    ),
                    isPositive = true
                )
            ),
            negativeExamples = listOf(
                FOLExample(
                    structure = FOLStructure(
                        constants = listOf(
                            FOLConstant("c", "Node"),
                            FOLConstant("d", "Node")
                        ),
                        relationFacts = mapOf(
                            "edge" to listOf(
                                listOf("c", "d")
                            )
                        )
                    ),
                    isPositive = false
                )
            ),
            maxNumOfNode = 5
        )

        val learner = FOLLearner(task)
        val solution = learner.learn()

        assert(solution != null)
        val formula = solution!!.getFOL()
        assert(formula.contains("∀") || formula.contains("∃"))
        println("Learned formula: $formula")

    }

    @Test
    fun testSimpleExists() {
        val task = FOLTask(
            sorts = listOf(FOLSort("Person")),
            relations = listOf(FOLRelation("friend", listOf("Person", "Person"))),
            functions = emptyList(),
            positiveExamples = listOf(
                FOLExample(
                    structure = FOLStructure(
                        constants = listOf(
                            FOLConstant("alice", "Person"),
                            FOLConstant("bob", "Person")
                        ),
                        relationFacts = mapOf(
                            "friend" to listOf(
                                listOf("alice", "bob")
                            )
                        )
                    ),
                    isPositive = true
                )
            ),
            negativeExamples = listOf(
                FOLExample(
                    structure = FOLStructure(
                        constants = listOf(
                            FOLConstant("charlie", "Person")
                        ),
                        relationFacts = mapOf(
                            "friend" to emptyList()
                        )
                    ),
                    isPositive = false
                )
            ),
            maxNumOfNode = 3
        )

        val learner = FOLLearner(task)
        val solution = learner.learn()

      assert(solution != null)
        val formula = solution!!.getFOL()
        solution.dumpInstance("full")
        println("Learned formula: $formula")

    }
}