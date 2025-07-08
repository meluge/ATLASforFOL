package cmu.s3d.fol.learning

import edu.mit.csail.sdg.parser.CompModule
import edu.mit.csail.sdg.parser.CompUtil
import edu.mit.csail.sdg.translator.A4Solution
import edu.mit.csail.sdg.translator.A4TupleSet
import edu.mit.csail.sdg.ast.Sig          // Alloy's signature class


class FOLLearningSolution(
    private val learner: FOLLearner,
    private val world: CompModule,
    private val alloySolution: A4Solution,
    private val numOfNode: Int,
    private val stepSize: Int
) {

    fun dumpInstance(tag: String = "") {
        for (sig in world.allReachableSigs) {
            val ts = alloySolution.eval(sig) as A4TupleSet
            println("${sig.label.padEnd(30)} = $ts")
            for (field in sig.fields) {
                val fset = alloySolution.eval(field) as A4TupleSet
                println("  ${field.label.padEnd(28)} = $fset")
            }
        }
    }

    init {
        for (a in alloySolution.allAtoms)
            world.addGlobal(a.label, a)
        for (a in alloySolution.allSkolems)
            world.addGlobal(a.label, a)
    }

    data class Node(val name: String, val left: String?, val right: String?)

    private val operatorMapping = mapOf(
        "Forall" to "∀",
        "Exists" to "∃",
        "Not" to "¬",
        "And" to "∧",
        "Or" to "∨",
        "Implies" to "→"
    )

    fun getFOL(): String {
        val root = getRoot()
        return getFOL(root)
    }

    fun getFOL2(): String {
        val root = getRoot()
        return getFOL2(root)
    }

    private fun getFOL(node: String): String {
        val (name, leftNode, rightNode) = getNodeAndChildren(node)
        val sigName = name.replace("\\d+$".toRegex(), "")
        return when {
            // Quantifier case
            isQuantifier(sigName) && leftNode != null && rightNode == null -> {
                val boundVar = getBoundVariable(node)
                val varSort = getVariableSort(node)
                "${getMappedOperator(sigName)}$boundVar:$varSort. ${getFOL(leftNode)}"
            }
            // Binary connective - use infix notation with proper parentheses
            leftNode != null && rightNode != null -> {
                val leftFormula = getFOL(leftNode)
                val rightFormula = getFOL(rightNode)
                val operator = getMappedOperator(sigName)

                when (sigName) {
                    "Implies" -> "($leftFormula → $rightFormula)"
                    "And" -> "($leftFormula ∧ $rightFormula)"
                    "Or" -> "($leftFormula ∨ $rightFormula)"
                    else -> "($leftFormula $operator $rightFormula)"
                }
            }
            leftNode != null && rightNode == null -> {
                val childFormula = getFOL(leftNode)
                val operator = getMappedOperator(sigName)
                "$operator$childFormula"
            }
            leftNode == null && rightNode == null -> {
                if (isAtom(node)) {
                    buildAtomString(node)
                } else {
                    name
                }
            }
            else -> error("Invalid FOL formula.")
        }
    }

    private fun getFOL2(node: String): String {
        val (name, leftNode, rightNode) = getNodeAndChildren(node)
        val sigName = name.replace("\\d+$".toRegex(), "")
        return when {
            // Quantifier case
            isQuantifier(sigName) && leftNode != null && rightNode == null -> {
                val boundVar = getBoundVariable(node)
                val varSort = getVariableSort(node)
                "${getMappedOperator(sigName)}$boundVar:$varSort. ${getFOL2(leftNode)}"
            }
            // Binary connective
            leftNode != null && rightNode != null -> {
                val leftFormula = getFOL2(leftNode)
                val rightFormula = getFOL2(rightNode)
                val operator = getMappedOperator(sigName)
                "($leftFormula $operator $rightFormula)"
            }
            // Unary connective
            leftNode != null && rightNode == null -> {
                val childFormula = getFOL2(leftNode)
                val operator = getMappedOperator(sigName)
                "$operator$childFormula"
            }
            // Atom case
            leftNode == null && rightNode == null -> {
                if (isAtom(node)) {
                    buildAtomString(node)
                } else {
                    name
                }
            }
            else -> error("Invalid FOL formula.")
        }
    }

    private fun getMappedOperator(name: String): String {
        return operatorMapping[name.replace("\\d+$".toRegex(), "")] ?: error("Invalid operator: $name")
    }

    private fun isQuantifier(name: String): Boolean {
        return name in listOf("Forall", "Exists")
    }

    private fun isAtom(node: String): Boolean {
        return try {
            val expr = CompUtil.parseOneExpression_fromString(world, "$node in Atom")
            when (val result = alloySolution.eval(expr)) {
                is Boolean -> result
                is A4TupleSet -> result.size() > 0
                else -> false
            }
        } catch (e: Exception) {
            e.printStackTrace()
            false
        }
    }

    private fun buildAtomString(node: String): String {
        try {
            val relationExpr = CompUtil.parseOneExpression_fromString(world, "$node.relation")
            val relation = (alloySolution.eval(relationExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
            val cleanRelation = relation?.replace("Rel", "")?.replace("⁰", "")?.replace("\\$\\d+".toRegex(), "") ?: "R"

            val termsList = mutableListOf<String>()


            val ordSig = world.allReachableSigs.find { it.label == "this/IdxOrder/Ord" || it.label == "IdxOrder/Ord" }
                ?: error("Could not find sig 'IdxOrder/Ord'")
            val firstField = ordSig.fields.find { it.label == "First" }
                ?: error("Could not find field 'First' on sig 'IdxOrder/Ord'")
            val nextField = ordSig.fields.find { it.label == "Next" }
                ?: error("Could not find field 'Next' on sig 'IdxOrder/Ord'")

            val firstRelation = alloySolution.eval(firstField) as A4TupleSet
            val nextRelation = alloySolution.eval(nextField) as A4TupleSet

            val nextMap = nextRelation.associate { it.atom(1) to it.atom(2) }

            var currentIdxAtom = firstRelation.firstOrNull()?.atom(1)?.toString()

            while (currentIdxAtom != null) {
                val termExpr = CompUtil.parseOneExpression_fromString(world, "($node.terms)[$currentIdxAtom]")
                val term = (alloySolution.eval(termExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()

                if (term != null) {
                    termsList.add(buildTermString(term))
                } else {
                    break
                }

                currentIdxAtom = nextMap[currentIdxAtom]?.toString()
            }

            return if (termsList.isNotEmpty()) {
                "$cleanRelation(${termsList.joinToString(",")})"
            } else {
                cleanRelation
            }

        } catch (e: Exception) {
            println("Exception in buildAtomString: ${e.message}")
            e.printStackTrace()
            return node.replace("⁰", "").replace("\\$\\d+".toRegex(), "")
        }
    }

    private fun getBoundVariable(node: String): String {
        return try {
            val expr = CompUtil.parseOneExpression_fromString(world, "$node.bound_var")
            val varAtom = (alloySolution.eval(expr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
            val result = varAtom?.replace("⁰", "")?.replace("\\$\\d+".toRegex(), "")?.lowercase() ?: "x"
            result
        } catch (e: Exception) {
            "x"
        }
    }

    private fun getVariableSort(node: String): String {
        return try {
            val expr = CompUtil.parseOneExpression_fromString(world, "$node.var_sort")
            val sortAtom = (alloySolution.eval(expr) as A4TupleSet).map { it.atom(0) }.firstOrNull() ?: "Sort"
            val result = sortAtom.replace("Sort", "").replace("⁰", "").replace("\\$\\d+".toRegex(), "").ifEmpty { "Sort" }
            result
        } catch (e: Exception) {
            "Sort"
        }
    }


    private fun buildTermString(term: String): String {
        return try {
            println("      Building term string for: $term")

            // var case
            try {
                val varExpr = CompUtil.parseOneExpression_fromString(world, "$term.var")
                val varResult = alloySolution.eval(varExpr) as A4TupleSet
                if (varResult.size() > 0) {
                    val variable = varResult.map { it.atom(0) }.firstOrNull()
                    println("      Variable found: $variable")
                    if (variable != null) {
                        val result = variable.replace("⁰", "").replace("\\$\\d+".toRegex(), "").lowercase()
                        println("      Variable result: $result")
                        return result
                    }
                }
            } catch (e: Exception) {
                println("      Not a variable term: ${e.message}")
            }

            // const case
            try {
                val constExpr = CompUtil.parseOneExpression_fromString(world, "$term.constant")
                val constResult = alloySolution.eval(constExpr) as A4TupleSet
                if (constResult.size() > 0) {
                    val constant = constResult.map { it.atom(0) }.firstOrNull()
                    println("      Constant found: $constant")
                    if (constant != null) {
                        val result = constant.replace("⁰", "").replace("\\$\\d+".toRegex(), "")
                        println("      Constant result: $result")
                        return result
                    }
                }
            } catch (e: Exception) {
                println("      Not a constant term: ${e.message}")
            }

            // func case
            try {
                val funcExpr = CompUtil.parseOneExpression_fromString(world, "$term.func")
                val funcResult = alloySolution.eval(funcExpr) as A4TupleSet
                if (funcResult.size() > 0) {
                    val function = funcResult.map { it.atom(0) }.firstOrNull()
                    println("      Function found: $function")
                    if (function != null) {
                        val argsList = mutableListOf<String>()
                        var i = 0
                        while (true) {
                            try {
                                val argExpr = CompUtil.parseOneExpression_fromString(world, "$term.args[I$i]")
                                val argResult = alloySolution.eval(argExpr) as A4TupleSet
                                val arg = argResult.map { it.atom(0) }.firstOrNull()
                                if (arg != null) {
                                    argsList.add(buildTermString(arg))
                                    i++
                                } else {
                                    break
                                }
                            } catch (e: Exception) {
                                break
                            }
                        }
                        val cleanFunc = function.replace("Func", "").replace("⁰", "").replace("\\$\\d+".toRegex(), "")
                        val result = "$cleanFunc(${argsList.joinToString(",")})"
                        println("      Function result: $result")
                        return result
                    }
                }
            } catch (e: Exception) {
                println("      Not a function term: ${e.message}")
            }

            val fallback = term.replace("⁰", "").replace("\\$\\d+".toRegex(), "")
            println("      Fallback result: $fallback")
            fallback

        } catch (e: Exception) {
            println("      Exception in buildTermString: ${e.message}")
            e.printStackTrace()
            term.replace("⁰", "").replace("\\$\\d+".toRegex(), "")
        }
    }


    fun getNodeAndChildren(node: String): Node {
        // Split on either $ or ⁰ to get the base name
        val name = node.split('$', '⁰')[0]

        val leftNode = when {
            isQuantifier(name) -> {
                // For quantifiers, the "left" child is the body
                try {
                    val expr = CompUtil.parseOneExpression_fromString(world, "$node.body")
                    (alloySolution.eval(expr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
                } catch (e: Exception) { null }
            }
            else -> {
                // For other formula types, try child first, then left
                try {
                    val expr = CompUtil.parseOneExpression_fromString(world, "$node.child")
                    val result = (alloySolution.eval(expr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
                    if (result != null) result else {
                        val leftExpr = CompUtil.parseOneExpression_fromString(world, "$node.left")
                        (alloySolution.eval(leftExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
                    }
                } catch (e: Exception) {
                    try {
                        val leftExpr = CompUtil.parseOneExpression_fromString(world, "$node.left")
                        (alloySolution.eval(leftExpr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
                    } catch (e2: Exception) { null }
                }
            }
        }

        val rightNode = try {
            val expr = CompUtil.parseOneExpression_fromString(world, "$node.right")
            (alloySolution.eval(expr) as A4TupleSet).map { it.atom(0) }.firstOrNull()
        } catch (e: Exception) { null }

        return Node(name, leftNode, rightNode)
    }

    fun getRoot(): String {
        val expr = CompUtil.parseOneExpression_fromString(world, "Separator.root")
        return (alloySolution.eval(expr) as A4TupleSet).map { it.atom(0) }.first()
    }

    fun next(): FOLLearningSolution? {
        val nextSolution = alloySolution.next()
        return if (nextSolution.satisfiable()) {
            FOLLearningSolution(learner, world, nextSolution, numOfNode, stepSize)
        } else {
            learner.learn(numOfNode + stepSize)
        }
    }

    fun debugFormulaStructure(): String {
        val root = getRoot()
        return debugNode(root, 0)
    }

    private fun debugNode(node: String, depth: Int): String {
        val indent = "  ".repeat(depth)
        val (name, leftNode, rightNode) = getNodeAndChildren(node)

        val result = StringBuilder()
        result.append("${indent}Node: $node\n")
        result.append("${indent}  Type: $name\n")

        if (isQuantifier(name)) {
            result.append("${indent}  BoundVar: ${getBoundVariable(node)}\n")
            result.append("${indent}  VarSort: ${getVariableSort(node)}\n")
        }

        if (isAtom(node)) {
            result.append("${indent}  AtomString: ${buildAtomString(node)}\n")
        }

        leftNode?.let {
            result.append("${indent}  Left:\n")
            result.append(debugNode(it, depth + 2))
        }

        rightNode?.let {
            result.append("${indent}  Right:\n")
            result.append(debugNode(it, depth + 2))
        }

        return result.toString()
    }
}
