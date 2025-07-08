package cmu.s3d.fol.samples2fol

import cmu.s3d.fol.samples2fol.FOLTaskParser
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class FOLTaskParserTests {
    @Test
    fun testJsonFormat() {
        val jsonContent = """
        {
            "sorts": ["Node"],
            "relations": [
                {"name": "edge", "signature": ["Node", "Node"]}
            ],
            "functions": [],
            "positiveExamples": [
                {
                    "constants": [
                        {"name": "a", "sort": "Node"},
                        {"name": "b", "sort": "Node"}
                    ],
                    "relationFacts": {
                        "edge": [["a", "b"], ["b", "a"]]
                    }
                }
            ],
            "negativeExamples": [
                {
                    "constants": [
                        {"name": "c", "sort": "Node"}
                    ],
                    "relationFacts": {
                        "edge": []
                    }
                }
            ],
            "maxNodes": 5
        }
        """.trimIndent()

        val task = FOLTaskParser.parseTask(jsonContent)

        assertEquals(1, task.sorts.size)
        assertEquals("Node", task.sorts[0].name)
        assertEquals(1, task.relations.size)
        assertEquals("edge", task.relations[0].name)
        assertEquals(1, task.positiveExamples.size)
        assertEquals(1, task.negativeExamples.size)
        assertEquals(5, task.maxNumOfNode)
    }

    @Test
    fun testSExprFormat() {
        val sexprContent = """
        (sort Node)
        (relation edge Node Node)
        (model + 
            ((a Node) (b Node))
            (edge a b)
            (edge b a)
        )
        (model -
            ((c Node))
        )
        """.trimIndent()

        val task = FOLTaskParser.parseTask(sexprContent)

        assertEquals(1, task.sorts.size)
        assertEquals(1, task.relations.size)
        assertEquals(1, task.positiveExamples.size)
        assertEquals(1, task.negativeExamples.size)
    }
}