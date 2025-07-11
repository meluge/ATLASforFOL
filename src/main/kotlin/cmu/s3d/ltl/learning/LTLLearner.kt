package cmu.s3d.fol.learning
import kotlin.math.pow


import cmu.s3d.fol.*
import edu.mit.csail.sdg.alloy4.A4Reporter
import edu.mit.csail.sdg.parser.CompUtil
import edu.mit.csail.sdg.translator.A4Options
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod
import kotlin.math.max
import kotlin.math.min

data class FOLTask(
    val sorts: List<FOLSort>,
    val relations: List<FOLRelation>,
    val functions: List<FOLFunction>,
    val positiveExamples: List<FOLExample>,
    val negativeExamples: List<FOLExample>,
    val maxNumOfNode: Int = 10,
    val maxQuantifiers: Int = 3,
    val excludedOperators: List<String> = emptyList(),
    val customConstraints: String = """
        fact OnlyVarTerms {
            all a: Atom | a in Separator.root.*all_children implies {
                all t: a.terms[Idx] | t in VarTerm
            }
        }
    """
)



class FOLLearner(
    private val task: FOLTask,
    customAlloyOptions: A4Options? = null,
    private val minimized: Boolean = true,
) : AlloyMaxBase(customAlloyOptions) {


    fun generateAlloyModel(scope: Int): String {
        val maxElements = max(
            task.positiveExamples.maxOfOrNull { it.structure.constants.size } ?: 0,
            task.negativeExamples.maxOfOrNull { it.structure.constants.size } ?: 0
        )

        val maxArity = max(
            task.relations.maxOfOrNull { it.arity } ?: 2,
            task.functions.maxOfOrNull { it.arity } ?: 2
        )

        val numVariables = task.maxQuantifiers
        val (generatedEnvs, envCount) = generateAllEnvironments(numVariables, maxElements)

        val alloyScript = """
        open util/ordering[Idx] as IdxOrder

        abstract sig Idx {}
        one sig ${(0 until maxArity).joinToString(", ") { "I$it" }} extends Idx {}

        fact IdxOrdering {
            IdxOrder/first = I0
            ${if (maxArity > 1) "IdxOrder/next = " + (0 until maxArity-1).joinToString(" + ") { "I$it->I${it+1}" } else "no IdxOrder/next"}
        }

        abstract sig Variable {}
        abstract sig Element {
            sort: one Sort
        }
        abstract sig Sort {}

        abstract sig Symbol {
            arity: one Int,
            signature: Idx -> Sort
        } {
            arity > 0
            all i: Idx | some signature[i] iff #(i.prevs + i) <= arity
        }

        abstract sig Tuple {
            tup : Idx -> lone Element
        } {
            all i: Idx | lone tup[i]
            some s: Symbol | #tup = s.arity
        }

        abstract sig Relation extends Symbol {}
        abstract sig Function extends Symbol {} {
            arity > 1
        }

        abstract sig Formula {}

        abstract sig Term {
            eval: Structure -> Environment -> lone Element
        }

        sig VarTerm extends Term {
            var: one Variable
        } {
            all s: Structure, env: Environment | eval[s][env] = env.mapping[var]
        }

        sig ConstTerm extends Term {
            constant: one Element
        } {
            all s: Structure, env: Environment |
                eval[s][env] = (constant & s.elements)
        }

        sig FuncTerm extends Term {
            func: one Function,
            args: Idx -> lone Term
        } {
            #args = func.arity.minus[1]
            all i: Idx | some args[i] iff #(i.prevs + i) < func.arity
        }

        fact FuncTermEvaluation {
            all s: Structure, ft: FuncTerm, env: Environment |
                ft.eval[s][env] = {e: Element |
                    some tuple: s.func_interpretation[ft.func] |
                        (all i: Idx | some ft_arg: ft.args[i] |
                            tuple.tup[i] in ft_arg.eval[s][env]) and
                        tuple.tup[last[ft.func.arity]] = e
                }
        }

        sig Atom extends Formula {
            relation: one Relation,
            terms: Idx -> lone Term
        } {
            #terms = relation.arity
            all i: Idx | some terms[i] iff #(i.prevs + i) <= relation.arity
        }

        abstract sig Quantifier extends Formula {
            bound_var: one Variable,
            var_sort: one Sort,
            body: one Formula
        }
        ${if ("Forall" !in task.excludedOperators) "sig Forall extends Quantifier {}" else ""}
        ${if ("Exists" !in task.excludedOperators) "sig Exists extends Quantifier {}" else ""}

        abstract sig UnaryConnective extends Formula {
            child: one Formula
        }
        ${if ("Not" !in task.excludedOperators) "sig Not extends UnaryConnective {}" else ""}

        abstract sig BinaryConnective extends Formula {
            left: one Formula,
            right: one Formula
        } {
            left != right
        }
        ${if ("And" !in task.excludedOperators) "sig And extends BinaryConnective {}" else ""}
        ${if ("Or" !in task.excludedOperators) "sig Or extends BinaryConnective {}" else ""}
        ${if ("Implies" !in task.excludedOperators) "sig Implies extends BinaryConnective {}" else ""}

        abstract sig Environment {
            mapping: Variable -> lone Element
        }
        one sig EmptyEnvironment extends Environment {} {
            no mapping
        }

        abstract sig Structure {
            elements: set Element,
            interpretation: Relation -> set Tuple,
            func_interpretation: Function -> set Tuple,
            satisfies: Environment -> set Formula
        }

        abstract sig PositiveStructure extends Structure {}
        abstract sig NegativeStructure extends Structure {}

        fun all_children : Formula -> Formula {
            (Quantifier <: body) + (UnaryConnective <: child) +
            (BinaryConnective <: (left + right))
        }

        fun extendEnv[env: Environment, v: Variable, e: Element]: Environment {
            {eEnv: Environment | eEnv.mapping = env.mapping ++ (v -> e)}
        }

        fun last[a: Int]: Idx { {i: Idx | #(i.prevs + i) = a} }
        fun getTerms[a: Atom]: set Term { a.terms[Idx] }

        fact Semantics {
            all s: Structure {
                all env: Environment, a: Atom |
                    (env -> a) in s.satisfies iff (
                        some t: s.interpretation[a.relation] |
                            all i: Idx | some term: a.terms[i] |
                                t.tup[i] in term.eval[s][env]
                    )
                ${if ("Not" !in task.excludedOperators) """
                all env: Environment, n: Not |
                    (env -> n) in s.satisfies iff (env -> n.child) not in s.satisfies
                """ else ""}
                ${if ("And" !in task.excludedOperators) """
                all env: Environment, a: And |
                    (env -> a) in s.satisfies iff ((env -> a.left) in s.satisfies and (env -> a.right) in s.satisfies)
                """ else ""}
                ${if ("Or" !in task.excludedOperators) """
                all env: Environment, o: Or |
                    (env -> o) in s.satisfies iff ((env -> o.left) in s.satisfies or (env -> o.right) in s.satisfies)
                """ else ""}
                ${if ("Implies" !in task.excludedOperators) """
                all env: Environment, i: Implies |
                    (env -> i) in s.satisfies iff (not (env -> i.left) in s.satisfies or (env -> i.right) in s.satisfies)
                """ else ""}
                ${if ("Forall" !in task.excludedOperators) """
                all env: Environment, f: Forall |
                    (env -> f) in s.satisfies iff
                    (all e: s.elements | e.sort = f.var_sort implies
                        (one enb: extendEnv[env, f.bound_var, e] | (enb -> f.body) in s.satisfies))
                """ else ""}
                ${if ("Exists" !in task.excludedOperators) """
                all env: Environment, e: Exists |
                    (env -> e) in s.satisfies iff
                    (some elem: s.elements | elem.sort = e.var_sort and
                        (one enb: extendEnv[env, e.bound_var, elem] | (enb -> e.body) in s.satisfies))
                """ else ""}
            }
        }

        fact FormulaStructure {
            all f: Formula - Separator.root | one f.~all_children
            Formula = Separator.root.*all_children
            no f: Formula | f in f.^all_children
        }

        fact WellFormedness {
            all f: Formula | some a: Atom | a in f.*all_children
            all a: Atom, vt: getTerms[a] & VarTerm |
                some q: Quantifier | q.bound_var = vt.var and a in q.^all_children
            all q: Quantifier |
                some a: Atom, vt: getTerms[a] & VarTerm |
                    vt.var = q.bound_var and a in q.^all_children
            all q1, q2: Quantifier |
                q2 in q1.^all_children implies q1.bound_var != q2.bound_var
            all a: Atom | #a.terms = a.relation.arity
        }
        
        fact QuantifierLimit {
             #Quantifier <= ${task.maxQuantifiers}
        }

        fact SyntacticRestrictions {
            all c: And + Or + Implies + Not | no (c.*all_children & Quantifier)
        }

        fact AvoidDegenerateFormulas {
            // Prevent double negation
            no n: Not | n.child in Not
            // Prevent trivial conjunctions/disjunctions like (p and p)
            no bc: BinaryConnective | bc.left = bc.right
            // Prevent redundant atoms
            no disj a1, a2: Atom | a1.relation = a2.relation and a1.terms = a2.terms
        }

        fact EnvironmentIsExtensional {
            all e1, e2: Environment | e1.mapping = e2.mapping implies e1 = e2
        }
        fact VarTermIsUnique {
            all vt1, vt2: VarTerm | vt1.var = vt2.var implies vt1 = vt2
        }
        fact ConstTermIsUnique {
            all ct1, ct2: ConstTerm | ct1.constant = ct2.constant implies ct1 = ct2
        }

        one sig Separator {
            root: one Formula
        }

        // --- Instance Specific Part ---
        one sig ${task.sorts.joinToString(", ") { "${it.name}Sort" }} extends Sort {}
        one sig ${(0 until numVariables).joinToString(", ") { "V$it" }} extends Variable {}
        ${generateElements(maxElements)}
        ${generateRelations()}
        ${generateFunctions()}
        ${generateStructureConstraints()}

        $generatedEnvs

        ${task.customConstraints}

        pred findSeparator {
            all p: PositiveStructure | (EmptyEnvironment -> Separator.root) in p.satisfies
            all n: NegativeStructure | (EmptyEnvironment -> Separator.root) not in n.satisfies
        }

        run { findSeparator } for $scope Formula, $scope Atom, ${task.maxQuantifiers} Quantifier,
        $numVariables Variable, ${task.positiveExamples.size + task.negativeExamples.size} Structure, $scope Term,
        $scope Tuple, ${envCount + 1} Environment,
        ${if (task.functions.isNotEmpty()) task.functions.size else "3"} Function
    """.trimIndent()

        return alloyScript
    }

    private fun generateElements(maxElements: Int): String {
        return (0 until maxElements).joinToString("\n        ") { index ->
            val sort = task.sorts.firstOrNull()?.name ?: "DefaultSort"
            "one sig E$index extends Element {} { sort = ${sort}Sort }"
        }
    }

    private fun generateRelations(): String {
        return task.relations.joinToString("\n        ") { rel ->
            """one sig ${rel.name}Rel extends Relation {} {
                arity = ${rel.arity}
                signature = ${rel.signature.mapIndexed { i, sort -> "I$i->${sort}Sort" }.joinToString(" + ")}
            }"""
        }
    }

    private fun generateFunctions(): String {
        return if (task.functions.isNotEmpty()) {
            task.functions.joinToString("\n        ") { func ->
                """one sig ${func.name}Func extends Function {} {
                    arity = ${func.arity}
                    signature = ${func.signature.mapIndexed { i, sort -> "I$i->${sort}Sort" }.joinToString(" + ")}
                }"""
            }
        } else ""
    }


    private fun generateStructureConstraints(): String {
        val structures = mutableListOf<String>()
        val facts = mutableListOf<String>()

        task.positiveExamples.forEachIndexed { index, example ->
            val structName = "PS$index"
            structures.add(generateSimpleStructure(structName, "PositiveStructure", example))
            facts.add(generateStructureFact(structName, example))
        }

        task.negativeExamples.forEachIndexed { index, example ->
            val structName = "NS$index"
            structures.add(generateSimpleStructure(structName, "NegativeStructure", example))
            facts.add(generateStructureFact(structName, example))
        }

        return structures.joinToString("\n        ") + "\n\n        " +
                facts.joinToString("\n        ")
    }

    private fun generateSimpleStructure(name: String, sig: String, example: FOLExample): String {
        return """one sig $name extends $sig {} {
            elements = ${example.structure.constants.indices.joinToString(" + ") { "E$it" }}
        }"""
    }

    private fun generateStructureFact(name: String, example: FOLExample): String {
        val elementMapping = example.structure.constants.mapIndexed { i, const -> const.name to "E$i" }.toMap()
        val constraints = mutableListOf<String>()

        task.relations.forEach { rel ->
            val facts = example.structure.relationFacts[rel.name] ?: emptyList()
            if (facts.isNotEmpty()) {
                facts.forEach { tuple ->
                    val mappedElements = tuple.map { elementMapping[it] ?: "E0" }
                    val constraint = "some t: $name.interpretation[${rel.name}Rel] | " +
                            mappedElements.mapIndexed { i, elem -> "t.tup[I$i] = $elem" }.joinToString(" and ")
                    constraints.add(constraint)
                }
                constraints.add("#$name.interpretation[${rel.name}Rel] = ${facts.size}")
            } else {
                constraints.add("no $name.interpretation[${rel.name}Rel]")
            }
        }

        constraints.add("no $name.func_interpretation")

        return """fact ${name}Constraints {
            ${constraints.joinToString("\n            ")}
        }"""
    }

    private fun generateAllEnvironments(numVars: Int, maxElements: Int): Pair<String, Int> {
        if (numVars == 0) return Pair("", 0)

        val variables = (0 until numVars).map { "V$it" }
        val elements = (0 until maxElements).map { "E$it" }
        val elementChoices = elements + listOf<String?>(null)

        var allMappings = listOf(mapOf<String, String?>())

        // Generate all possible mappings by computing the Cartesian product
        for (variable in variables) {
            val nextMappings = mutableListOf<Map<String, String?>>()
            for (mapping in allMappings) {
                for (choice in elementChoices) {
                    nextMappings.add(mapping + (variable to choice))
                }
            }
            allMappings = nextMappings
        }

        val finalMappings = allMappings.filter { it.values.any { v -> v != null } }

        val environmentDefs = finalMappings.mapIndexed { index, mapping ->
            val mappingStr = mapping.entries
                .filter { it.value != null }
                .joinToString(" + ") { (v, e) -> "$v->$e" }
            "one sig Env${index + 1} extends Environment {} { mapping = $mappingStr }"
        }

        return Pair(environmentDefs.joinToString("\n        "), finalMappings.size)
    }


    fun learn(start: Int? = null, stepSize: Int = 2): FOLLearningSolution? {
        val startNum = start ?: min(max((task.maxNumOfNode - task.sorts.size) / 2, 3), 6)
        val nodesSeq = (startNum.. task.maxNumOfNode step stepSize).toMutableList()
        if (nodesSeq.isEmpty() || nodesSeq.last() < task.maxNumOfNode)
            nodesSeq.add(task.maxNumOfNode)

        for (n in nodesSeq) {
            val alloyScript = generateAlloyModel(n)

            println("=== GENERATED ALLOY CODE (Scope: $n) ===")
            println(alloyScript)
            println("=== END ALLOY CODE ===")

            val reporter = A4Reporter.NOP
            val world = CompUtil.parseEverything_fromString(reporter, alloyScript)
            val options = alloyOptions()
            val command = world.allCommands.first()
            val solution = TranslateAlloyToKodkod.execute_command(reporter, world.allReachableSigs, command, options)

            if (solution.satisfiable()) {
                println("Found a satisfying solution with scope $n.")
                return FOLLearningSolution(this, world, solution, n, stepSize)
            }
        }

        return null
    }
}
