package cmu.s3d.ltl.samples2ltl

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class TaskParserTests {
    @Test
    fun testExample0000() {
        val content = ClassLoader.getSystemResource("samples2ltl/example0000.trace").readText()
        val task = TaskParser.parseTask(content)

        assertEquals(5, task.numOfPositives())
        assertEquals(5, task.numOfNegatives())
        assertEquals(2, task.depth)
        assertEquals(2, task.numOfVariables())
        assertEquals(5, task.maxLengthOfTraces())
        assertEquals("G(!(x0))", task.expected)

        val solution = task.buildLearner().learn()
        assert(solution != null)
        assertEquals(
            task.expected,
            solution!!.getLTL2()
        )
    }
}