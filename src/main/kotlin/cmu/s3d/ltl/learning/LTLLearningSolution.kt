package cmu.s3d.ltl.learning

import edu.mit.csail.sdg.parser.CompModule
import edu.mit.csail.sdg.parser.CompUtil
import edu.mit.csail.sdg.translator.A4Solution
import edu.mit.csail.sdg.translator.A4TupleSet

class LTLLearningSolution(private val world: CompModule, private val alloySolution: A4Solution) {

    fun getLTL(): String {
        val root = getRoot()
        return getLTL(root)
    }

    private fun getLTL(node: String): String {
        val name = node.split('$')[0]
        val leftExpr = CompUtil.parseOneExpression_fromString(world, "$node.l")
        val leftNode = (alloySolution.eval(leftExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
        val rightExpr = CompUtil.parseOneExpression_fromString(world, "$node.r")
        val rightNode = (alloySolution.eval(rightExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
        return when {
            leftNode == null && rightNode == null -> name
            leftNode != null && rightNode == null -> "($name ${getLTL(leftNode)})"
            leftNode != null && rightNode != null -> "($name ${getLTL(leftNode)} ${getLTL(rightNode)})"
            else -> error("Invalid LTL formula.")
        }
    }

    private fun getRoot(): String {
        val expr = CompUtil.parseOneExpression_fromString(world, "root")
        return (alloySolution.eval(expr) as A4TupleSet).map { it.atom(0) }.first()
    }

    fun next(): LTLLearningSolution? {
        val nextSolution = alloySolution.next()
        return if (nextSolution.satisfiable()) {
            LTLLearningSolution(world, nextSolution)
        } else {
            null
        }
    }
}