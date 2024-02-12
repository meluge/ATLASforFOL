package cmu.s3d.ltl.learning

import edu.mit.csail.sdg.parser.CompModule
import edu.mit.csail.sdg.parser.CompUtil
import edu.mit.csail.sdg.translator.A4Solution
import edu.mit.csail.sdg.translator.A4TupleSet

class LTLLearningSolution(private val world: CompModule, private val alloySolution: A4Solution) {

    data class Node(val name: String, val left: String?, val right: String?)

    private val operatorMapping = mapOf(
        "G"  to "G",
        "F"  to "F",
        "Neg"  to "!",
        "Until"  to "U",
        "And"  to "&",
        "Or"  to "|",
        "Imply" to "->",
        "X"  to "X"
    )

    fun getLTL(): String {
        val root = getRoot()
        return getLTL(root)
    }

    fun getLTL2(): String {
        val root = getRoot()
        return getLTL2(root)
    }

    private fun getLTL(node: String): String {
        val (name, leftNode, rightNode) = getNodeAndChildren(node)
        return when {
            leftNode == null && rightNode == null -> name
            leftNode != null && rightNode == null -> "($name ${getLTL(leftNode)})"
            leftNode != null && rightNode != null -> "($name ${getLTL(leftNode)} ${getLTL(rightNode)})"
            else -> error("Invalid LTL formula.")
        }
    }

    private fun getLTL2(node: String): String {
        val (name, leftNode, rightNode) = getNodeAndChildren(node)
        return when {
            leftNode == null && rightNode == null -> name
            leftNode != null && rightNode == null -> "${operatorMapping[name]}(${getLTL2(leftNode)})"
            leftNode != null && rightNode != null -> "${operatorMapping[name]}(${getLTL2(leftNode)},${getLTL2(rightNode)})"
            else -> error("Invalid LTL formula.")
        }
    }

    fun getNodeAndChildren(node: String): Node {
        val name = node.split('$')[0]
        val leftExpr = CompUtil.parseOneExpression_fromString(world, "$node.l")
        val leftNode = (alloySolution.eval(leftExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
        val rightExpr = CompUtil.parseOneExpression_fromString(world, "$node.r")
        val rightNode = (alloySolution.eval(rightExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
        return Node(name, leftNode, rightNode)
    }

    fun getRoot(): String {
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