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
    val maxNumOfNode: Int = 4,
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


    fun generateAlloyModel(): String {
        val maxElements = max(
            task.positiveExamples.maxOfOrNull { it.structure.constants.size } ?: 0,
            task.negativeExamples.maxOfOrNull { it.structure.constants.size } ?: 0
        )

        val maxArity = max(
            task.relations.maxOfOrNull { it.arity } ?: 2,
            task.functions.maxOfOrNull { it.arity } ?: 2
        )

        val numVariables = 4
        val numEnvironments = minOf(15, maxElements * numVariables + maxElements * maxElements)

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
            // The evaluation of a constant is the constant itself, but only if
            // it exists in the structure's set of elements.
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
                        (all i: Idx | some ft.args[i] implies
                            tuple.tup[i] = ft.args[i].eval[s][env]) and
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
        } {
            all f: Function |
                all t1, t2: func_interpretation[f] |
                    (all i: Idx | i != last[f.arity] implies t1.tup[i] = t2.tup[i])
                    implies t1 = t2
            
            // Type safety: elements in tuples must match relation signatures
            all r: Relation, t: interpretation[r] |
                all i: Idx | some t.tup[i] implies 
                    t.tup[i].sort = r.signature[i]
                    
            // Type safety for function interpretations
            all f: Function, t: func_interpretation[f] |
                all i: Idx | some t.tup[i] implies 
                    t.tup[i].sort = f.signature[i]
        }

        abstract sig PositiveStructure extends Structure {}
        abstract sig NegativeStructure extends Structure {}

        fun all_children : Formula -> Formula {
            (Quantifier <: body) + (UnaryConnective <: child) +
            (BinaryConnective <: left) + (BinaryConnective <: right)
        }

        fun extendEnv[env: Environment, v: Variable, e: Element]: Environment {
            {eEnv: Environment | eEnv.mapping = env.mapping ++ (v -> e)}
        }

        fun last[a: Int]: Idx {
            {i: Idx | #(i.prevs + i) = a}
        }

        fun getTerms[a: Atom]: set Term {
            a.terms[Idx]
        }

        fun getSubterms[t: FuncTerm]: set Term {
            t.args[Idx]
        }

        fun funcDeps: Term -> Term {
            {t: FuncTerm, t': Term | t' in t.args[Idx]}
        }

        fact Semantics {
            all s: Structure {
                all env: Environment, a: Atom |
                    (env -> a) in s.satisfies iff (
                        some t: s.interpretation[a.relation] |
                            all i: Idx | some a.terms[i] implies
                                t.tup[i] = a.terms[i].eval[s][env]
                    )

                ${if ("Not" !in task.excludedOperators) """
                all env: Environment, n: Not |
                    (env -> n) in s.satisfies iff
                    (env -> n.child) not in s.satisfies
                """ else ""}

                ${if ("And" !in task.excludedOperators) """
                all env: Environment, a: And |
                    (env -> a) in s.satisfies iff
                    ((env -> a.left) in s.satisfies and (env -> a.right) in s.satisfies)
                """ else ""}

                ${if ("Or" !in task.excludedOperators) """
                all env: Environment, o: Or |
                    (env -> o) in s.satisfies iff
                    ((env -> o.left) in s.satisfies or (env -> o.right) in s.satisfies)
                """ else ""}

                ${if ("Implies" !in task.excludedOperators) """
                all env: Environment, i: Implies |
                    (env -> i) in s.satisfies iff
                    ((env -> i.left) not in s.satisfies or (env -> i.right) in s.satisfies)
                """ else ""}

                ${if ("Forall" !in task.excludedOperators) """
                all env: Environment, f: Forall |
                    (env -> f) in s.satisfies iff
                    (all e: s.elements | e.sort = f.var_sort implies
                        let enb = extendEnv[env, f.bound_var, e] |
                        one enb and (enb -> f.body) in s.satisfies)
                """ else ""}

                ${if ("Exists" !in task.excludedOperators) """
                all env: Environment, e: Exists |
                    (env -> e) in s.satisfies iff
                    (some elem: s.elements | elem.sort = e.var_sort and
                        let enb = extendEnv[env, e.bound_var, elem] |
                        one enb and (enb -> e.body) in s.satisfies)
                """ else ""}
            }
        }

        fact FormulaStructure {
            // Every formula except the root has exactly one parent
            all f: Formula - Separator.root | one all_children.f
            
            // The formula tree is exactly the closure of the root
            Formula = Separator.root.*all_children
            
            // No formula is its own ancestor (acyclicity)
            no f: Formula | f in f.^all_children
        }

       fact WellFormedness {
            // Root must be a quantifier
            // Separator.root in Quantifier
            
            // All formulas must eventually lead to atoms
            all f: Formula | some a: Atom | a in f.*all_children
            
            // All variables in atoms must be bound by a quantifier
            all a: Atom, vt: getTerms[a] & VarTerm |
                some q: Quantifier | q.bound_var = vt.var and a in q.^all_children
            
            // For function terms containing variables
            all a: Atom, ft: getTerms[a] & FuncTerm, vt: getSubterms[ft] & VarTerm |
                some q: Quantifier | q.bound_var = vt.var and a in q.^all_children
            
            // Remove the requirement that all quantified variables must be used
            // This was preventing valid formulas
            
            // No repeated bound variables in nested quantifiers
            all q1, q2: Quantifier |
                q2 in q1.^all_children implies q1.bound_var != q2.bound_var
            
            // Ensure atoms have proper terms
            all a: Atom | #a.terms = a.relation.arity
            
            all q: Quantifier |
        some a: Atom | a in q.^all_children and
            (some vt: getTerms[a] & VarTerm | vt.var = q.bound_var or
             some ft: getTerms[a] & FuncTerm, vt: getSubterms[ft] & VarTerm | 
                vt.var = q.bound_var)
        }
        
       fact AvoidDegenerateFormulas {
        no n1, n2: Not | n2 = n1.child
        no disj a1, a2: Atom |
            a1.relation = a2.relation and a1.terms = a2.terms
            
        no bc: BinaryConnective | bc.left = bc.right
    }

       
        fact PreventMixedAtoms {
            // Each atom should be either all constants OR all variables, not mixed
            all a: Atom |
                (all t: getTerms[a] | t in ConstTerm) or
                (all t: getTerms[a] | t in VarTerm)
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

        // Generate concrete sorts
        one sig ${task.sorts.joinToString(", ") { "${it.name}Sort" }} extends Sort {}

        // Generate variables
        one sig ${(0 until 4).joinToString(", ") { "V$it" }} extends Variable {}

        // Generate elements/constants
        ${generateElements(maxElements)}

        // Define relations with type signatures
        ${task.relations.joinToString("\n        ") { rel ->
            """one sig ${rel.name}Rel extends Relation {} {
                arity = ${rel.arity}
                signature = ${rel.signature.mapIndexed { i, sort -> "I$i->${sort}Sort" }.joinToString(" + ")}
            }"""
        }}

        // Define functions with type signatures
        ${if (task.functions.isNotEmpty()) {
            task.functions.joinToString("\n        ") { func ->
                """one sig ${func.name}Func extends Function {} {
                    arity = ${func.arity}
                    signature = ${func.signature.mapIndexed { i, sort -> "I$i->${sort}Sort" }.joinToString(" + ")}
                }"""
            }
        } else ""}

        ${generateStructureConstraints()}

        // Generate explicit environments
         ${generateEnvironments(maxElements, numEnvironments)}

        ${task.customConstraints}

        pred findSeparator {
            all p: PositiveStructure | (EmptyEnvironment -> Separator.root) in p.satisfies
            all n: NegativeStructure | (EmptyEnvironment -> Separator.root) not in n.satisfies
        }

        run runseparator {
            findSeparator
            }   for ${task.maxNumOfNode}  Formula, ${task.maxNumOfNode} Atom, ${task.maxNumOfNode} Quantifier, 
        4 Variable, ${task.positiveExamples.size + task.negativeExamples.size + 2} Structure, ${task.maxNumOfNode} Term, 
        ${task.maxNumOfNode} Tuple, ${numEnvironments } Environment, 
        ${if (task.functions.isNotEmpty()) task.functions.size else "3"} Function
    """.trimIndent()


        return alloyScript
    }

    private fun generateElements(maxElements: Int): String {
        return (0 until maxElements).joinToString("\n        ") { index ->
            val sort = task.sorts.firstOrNull()?.name ?: "Person"
            "one sig E$index extends Element {} { sort = ${sort}Sort }"
        }
    }

    private fun generateStructureConstraints(): String {
        val structures = mutableListOf<String>()
        val facts = mutableListOf<String>()

        // Generate positive structures
        task.positiveExamples.forEachIndexed { index, example ->
            val structName = "PS$index"
            structures.add(generateSimpleStructure(structName, "PositiveStructure", example))
            facts.add(generateStructureFact(structName, example))
        }

        // Generate negative structures
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

        // Generate relation constraints
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

        // Generate function constraints
        constraints.add("no $name.func_interpretation")

        return """fact ${name}Constraints {
            ${constraints.joinToString("\n            ")}
        }"""
    }

    private fun generateEnvironments(maxElements: Int, numEnvironments: Int): String {
        val environmentDefs = mutableListOf<String>()

        var envIndex = 1

        for (v in 0 until minOf(4, numEnvironments / maxElements)) {
            for (e in 0 until maxElements) {
                if (envIndex <= numEnvironments) {
                    environmentDefs.add("one sig Env$envIndex extends Environment {} { mapping = V$v->E$e }")
                    envIndex++
                }
            }
        }

        if (maxElements >= 2 && envIndex <= numEnvironments) {
            for (e1 in 0 until minOf(maxElements, 3)) {
                for (e2 in 0 until minOf(maxElements, 3)) {
                    if (envIndex <= numEnvironments) {
                        environmentDefs.add("one sig Env$envIndex extends Environment {} { mapping = V0->E$e1 + V1->E$e2 }")
                        envIndex++
                    }
                }
            }
        }

        return """
        ${environmentDefs.joinToString("\n        ")}

        fact AllEnvironments {
            no EmptyEnvironment.mapping
        }
    """.trimIndent()
    }

    fun learn(start: Int? = null, stepSize: Int = 2): FOLLearningSolution? {
        val startNum = start ?: min(max((task.maxNumOfNode - task.sorts.size) / 2, 3), 6)
        val nodesSeq = (startNum.. task.maxNumOfNode step stepSize).toMutableList()
        if (nodesSeq.isEmpty() || nodesSeq.last() < task.maxNumOfNode)
            nodesSeq.add(task.maxNumOfNode)

        val alloyTemplate = generateAlloyModel()

        println("=== GENERATED ALLOY CODE ===")
        println(alloyTemplate)
        println("=== END ALLOY CODE ===")

        for (n in nodesSeq) {
            val alloyScript = String.format(alloyTemplate, n)

            val reporter = A4Reporter.NOP
            val world = CompUtil.parseEverything_fromString(reporter, alloyScript)
            val options = alloyOptions()
            val command = world.allCommands.first()
            val solution = TranslateAlloyToKodkod.execute_command(reporter, world.allReachableSigs, command, options)

            if (solution.satisfiable()) {
                return FOLLearningSolution(this, world, solution, n, stepSize)
            }
        }

        return null
    }
}