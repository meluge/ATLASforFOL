package cmu.s3d.fol.learning

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
    val maxQuantifiers: Int = 3, // New: Limit the number of quantifiers
    val excludedOperators: List<String> = emptyList(),
    val customConstraints: String = ""

)

/** A reference to a typed element atom, e.g. sort="epoch", idx=1 -> "Eepoch1". */
private data class ElemRef(val sort: String, val idx: Int) { val atom get() = "E$sort$idx" }

/** A concrete (typed) variable->element assignment, used to precompute atom truth tables. */
private data class EnvInfo(val name: String, val mapping: Map<String, ElemRef>)

class FOLLearner(
    private val task: FOLTask,
    customAlloyOptions: A4Options? = null,
    private val minimized: Boolean = true,
) : AlloyMaxBase(customAlloyOptions) {

    /** Per-sort global element count = max over all structures of that sort's constant count. */
    private fun sortElemCounts(): Map<String, Int> {
        val all = task.positiveExamples + task.negativeExamples
        return task.sorts.associate { s ->
            s.name to (all.maxOfOrNull { ex -> ex.structure.constants.count { it.sort == s.name } } ?: 0)
        }
    }

    /** Sorts that actually have elements; only these can carry quantified variables. */
    private fun usableSorts(): List<String> =
        sortElemCounts().filter { it.value > 0 }.keys.toList()

    /** All ways to split `total` variable slots across the usable sorts. */
    private fun sortDistributions(sorts: List<String>, total: Int): List<Map<String, Int>> {
        if (sorts.isEmpty()) return listOf(emptyMap())
        if (sorts.size == 1) return listOf(mapOf(sorts[0] to total))
        val result = mutableListOf<Map<String, Int>>()
        for (i in 0..total) {
            for (rest in sortDistributions(sorts.drop(1), total - i)) {
                result.add(mapOf(sorts[0] to i) + rest)
            }
        }
        return result
    }

    private fun defaultDistribution(): Map<String, Int> {
        val usable = usableSorts()
        if (usable.isEmpty()) return emptyMap()
        return sortDistributions(usable, task.maxQuantifiers).first()
    }

    fun generateAlloyModel(scope: Int, distribution: Map<String, Int> = defaultDistribution()): String {
        val sortElemCount = sortElemCounts()
        val maxArity = max(task.relations.maxOfOrNull { it.arity } ?: 2, 1)
        val numVariables = distribution.values.sum()
        val environments = generateEnvironments(distribution, sortElemCount)

        // `scope` bounds the number of Formula nodes. The only other sig governed by
        // the default scope is Term; VarTermIsUnique caps it at the variable count.
        // Everything else is fixed by explicit `one sig` declarations.
        val termBound = max(numVariables, 1)

        val alloyScript = """
        open util/ordering[Idx] as IdxOrder

        abstract sig Idx {}
        one sig ${(0 until maxArity).joinToString(", ") { "I$it" }} extends Idx {}

        fact IdxOrdering {
            IdxOrder/first = I0
            ${if (maxArity > 1) "IdxOrder/next = " + (0 until maxArity-1).joinToString(" + ") { "I$it->I${it+1}" } else "no IdxOrder/next"}
        }

        // Each variable carries a fixed sort (vsort); quantifier var_sort is tied to it
        // and atoms are required to be well-typed. This prunes ill-typed formulas and,
        // via sort-restricted environments, the assignment space.
        abstract sig Variable {
            vsort: one Sort
        }
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

        abstract sig Relation extends Symbol {} {
            arity > 0
        }

        abstract sig Formula {}

        // Terms are variables only. Atom evaluation is precomputed into the
        // per-structure `trueAtoms_*` tables, so terms no longer carry an `eval`.
        abstract sig Term {}
        sig VarTerm extends Term {
            var: one Variable
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
            // Only the environments binding variables to THIS structure's elements.
            envs: set Environment,
            satisfies: Environment -> set Formula${task.relations.joinToString("") { rel ->
            ",\n            trueAtoms_${rel.name}: Environment${" -> Variable".repeat(rel.arity)}"
        }}
        }

        abstract sig PositiveStructure extends Structure {}
        abstract sig NegativeStructure extends Structure {}

        fun extendEnv[env: Environment, v: Variable, e: Element]: Environment {
            {eEnv: Environment | eEnv.mapping = env.mapping ++ (v -> e)}
        }

        fun getTerms[a: Atom]: set Term { a.terms[Idx] }

        fact SortTyping {
            all q: Quantifier | q.var_sort = q.bound_var.vsort
            all a: Atom | all i: Idx | some a.terms[i] implies a.terms[i].var.vsort = a.relation.signature[i]
        }

        fact Semantics {
            all s: Structure {
                // Atom truth is a direct lookup in the precomputed table.
                all env: s.envs, a: Atom |
                    (env -> a) in s.satisfies iff (
                        ${task.relations.joinToString("\n                        or ") { rel ->
            val vars = (0 until rel.arity).joinToString(" -> ") { "a.terms[I$it].var" }
            "(a.relation = ${rel.name}Rel and (env -> $vars) in s.trueAtoms_${rel.name})"
        }}
                    )
                ${if ("Not" !in task.excludedOperators) """
                all env: s.envs, n: Not |
                    (env -> n) in s.satisfies iff (env -> n.child) not in s.satisfies
                """ else ""}
                ${if ("And" !in task.excludedOperators) """
                all env: s.envs, a: And |
                    (env -> a) in s.satisfies iff ((env -> a.left) in s.satisfies and (env -> a.right) in s.satisfies)
                """ else ""}
                ${if ("Or" !in task.excludedOperators) """
                all env: s.envs, o: Or |
                    (env -> o) in s.satisfies iff ((env -> o.left) in s.satisfies or (env -> o.right) in s.satisfies)
                """ else ""}
                ${if ("Implies" !in task.excludedOperators) """
                all env: s.envs, i: Implies |
                    (env -> i) in s.satisfies iff (not (env -> i.left) in s.satisfies or (env -> i.right) in s.satisfies)
                """ else ""}
                ${if ("Forall" !in task.excludedOperators) """
                all env: s.envs, f: Forall |
                    (env -> f) in s.satisfies iff
                    (all e: s.elements | e.sort = f.var_sort implies
                        (one enb: extendEnv[env, f.bound_var, e] | (enb -> f.body) in s.satisfies))
                """ else ""}
                ${if ("Exists" !in task.excludedOperators) """
                all env: s.envs, e: Exists |
                    (env -> e) in s.satisfies iff
                    (some elem: s.elements | elem.sort = e.var_sort and
                        (one enb: extendEnv[env, e.bound_var, elem] | (enb -> e.body) in s.satisfies))
                """ else ""}
            }
        }

        fact StructureAndWellFormedness {
            let all_children = (Quantifier <: body) + (UnaryConnective <: child) + (BinaryConnective <: (left + right)) | {
                // FormulaStructure constraints
                all f: Formula - Separator.root | one f.~all_children
                Formula = Separator.root.*all_children
                no f: Formula | f in f.^all_children

                // WellFormedness constraints
                all f: Formula | some a: Atom | a in f.*all_children
                all a: Atom, vt: getTerms[a] & VarTerm |
                    some q: Quantifier | q.bound_var = vt.var and a in q.^all_children
                all q: Quantifier |
                    some a: Atom, vt: getTerms[a] & VarTerm |
                        vt.var = q.bound_var and a in q.^all_children
                all q1, q2: Quantifier |
                    q2 in q1.^all_children implies q1.bound_var != q2.bound_var
                all a: Atom | #a.terms = a.relation.arity

                 all c: And + Or + Implies + Not | no (c.*all_children & Quantifier)  all c: And + Or + Implies + Not | no (c.*all_children & Quantifier)

                   all a: Atom | a in Separator.root.*all_children implies {
                all t: a.terms[Idx] | t in VarTerm
            } }
        }

        fact QuantifierLimit {
             #Quantifier <= ${task.maxQuantifiers}
        }

        fact AvoidDegenerateFormulas {
            no n: Not | n.child in Not
            no bc: BinaryConnective | bc.left = bc.right
            no disj a1, a2: Atom | a1.relation = a2.relation and a1.terms = a2.terms
        }

        fact EnvironmentIsExtensional {
            all e1, e2: Environment | e1.mapping = e2.mapping implies e1 = e2
        }
        fact VarTermIsUnique {
            all vt1, vt2: VarTerm | vt1.var = vt2.var implies vt1 = vt2
        }

        one sig Separator {
            root: one Formula
        }

        // --- Instance Specific Part ---
        one sig ${task.sorts.joinToString(", ") { "${it.name}Sort" }} extends Sort {}
        ${generateVariables(distribution)}
        ${generateElements(sortElemCount)}
        ${generateRelations()}
        ${generateStructures(environments, distribution, sortElemCount)}

        ${environmentDefs(environments)}

        ${task.customConstraints}

        pred findSeparator {
            all p: PositiveStructure | (EmptyEnvironment -> Separator.root) in p.satisfies
            all n: NegativeStructure | (EmptyEnvironment -> Separator.root) not in n.satisfies
        }

        run { findSeparator } for $scope but $termBound Term
    """.trimIndent()

        return alloyScript
    }

    private fun generateVariables(distribution: Map<String, Int>): String {
        val lines = mutableListOf<String>()
        for (s in task.sorts) {
            for (i in 0 until (distribution[s.name] ?: 0)) {
                lines.add("one sig V${s.name}$i extends Variable {} { vsort = ${s.name}Sort }")
            }
        }
        return lines.joinToString("\n        ")
    }

    private fun generateElements(sortElemCount: Map<String, Int>): String {
        val lines = mutableListOf<String>()
        for (s in task.sorts) {
            for (i in 0 until (sortElemCount[s.name] ?: 0)) {
                lines.add("one sig E${s.name}$i extends Element {} { sort = ${s.name}Sort }")
            }
        }
        return lines.joinToString("\n        ")
    }

    private fun generateRelations(): String {
        return task.relations.joinToString("\n        ") { rel ->
            """one sig ${rel.name}Rel extends Relation {} {
                arity = ${rel.arity}
                signature = ${rel.signature.mapIndexed { i, sort -> "I$i->${sort}Sort" }.joinToString(" + ")}
            }"""
        }
    }

    /** Emits each example as a structure sig plus a fact fixing its precomputed atom tables. */
    private fun generateStructures(
        environments: List<EnvInfo>,
        distribution: Map<String, Int>,
        sortElemCount: Map<String, Int>
    ): String {
        val blocks = mutableListOf<String>()

        fun emit(name: String, kind: String, ex: FOLExample) {
            // Map each constant to a typed element atom (k-th constant of sort S -> E{S}{k}).
            val perSort = mutableMapOf<String, Int>()
            val constToElem = LinkedHashMap<String, String>()
            for (c in ex.structure.constants) {
                val k = perSort.getOrDefault(c.sort, 0)
                constToElem[c.name] = "E${c.sort}$k"
                perSort[c.sort] = k + 1
            }
            val elems = if (constToElem.isEmpty()) "none" else constToElem.values.joinToString(" + ")

            // This structure's environments: those binding every variable within its
            // per-sort element range.
            val structEnvs = environments.filter { env ->
                env.mapping.values.all { ref -> ref.idx < (perSort[ref.sort] ?: 0) }
            }
            val envNames = listOf("EmptyEnvironment") + structEnvs.map { it.name }
            blocks.add(
                "one sig $name extends $kind {} {\n" +
                "            elements = $elems\n" +
                "            envs = ${envNames.joinToString(" + ")}\n" +
                "        }"
            )

            val factLines = task.relations.map { rel ->
                val entries = trueAtomEntries(ex, rel, structEnvs, constToElem, distribution)
                if (entries.isEmpty()) "no $name.trueAtoms_${rel.name}"
                else "$name.trueAtoms_${rel.name} = ${entries.joinToString(" + ")}"
            }
            blocks.add("fact ${name}Facts {\n            ${factLines.joinToString("\n            ")}\n        }")
        }

        task.positiveExamples.forEachIndexed { i, ex -> emit("PS$i", "PositiveStructure", ex) }
        task.negativeExamples.forEachIndexed { i, ex -> emit("NS$i", "NegativeStructure", ex) }
        return blocks.joinToString("\n        ")
    }

    /**
     * Precomputes, for one example and one relation, the (environment, well-typed
     * variable-vector) pairs under which rel(env(v0),..,env(vk)) holds in the example.
     */
    private fun trueAtomEntries(
        ex: FOLExample,
        rel: FOLRelation,
        environments: List<EnvInfo>,
        constToElem: Map<String, String>,
        distribution: Map<String, Int>
    ): List<String> {
        val factTuples = (ex.structure.relationFacts[rel.name] ?: emptyList())
            .mapNotNull { tuple ->
                val mapped = tuple.map { constToElem[it] }
                if (mapped.size == rel.arity && mapped.all { it != null }) mapped.filterNotNull() else null
            }.toSet()
        if (factTuples.isEmpty()) return emptyList()

        // For each position, only variables whose sort matches the relation's signature.
        val varsBySort = task.sorts.associate { s ->
            s.name to (0 until (distribution[s.name] ?: 0)).map { "V${s.name}$it" }
        }
        val positionVars = rel.signature.map { varsBySort[it] ?: emptyList() }
        if (positionVars.any { it.isEmpty() }) return emptyList()
        val vectors = cartesianVars(positionVars)

        val entries = mutableListOf<String>()
        for (env in environments) {
            for (vec in vectors) {
                val elemTuple = vec.map { env.mapping[it]?.atom }
                if (elemTuple.any { it == null }) continue
                if (elemTuple.filterNotNull() in factTuples) {
                    entries.add("${env.name} -> ${vec.joinToString(" -> ")}")
                }
            }
        }
        return entries
    }

    private fun cartesianVars(positionVars: List<List<String>>): List<List<String>> {
        var result = listOf<List<String>>(emptyList())
        for (opts in positionVars) {
            val next = mutableListOf<List<String>>()
            for (r in result) for (o in opts) next.add(r + o)
            result = next
        }
        return result
    }

    /**
     * Sort-restricted environments: the product, across sorts, of per-sort prefix
     * assignments. Within each sort, variables are bound in index order (a symmetry
     * break) to that sort's elements; sorts interleave freely. Excludes the empty
     * assignment, which is the global EmptyEnvironment.
     */
    private fun generateEnvironments(
        distribution: Map<String, Int>,
        sortElemCount: Map<String, Int>
    ): List<EnvInfo> {
        fun perSortPrefixes(sort: String): List<Map<String, ElemRef>> {
            val slots = distribution[sort] ?: 0
            val elems = sortElemCount[sort] ?: 0
            val all = mutableListOf<Map<String, ElemRef>>(emptyMap())
            var prev = listOf<Map<String, ElemRef>>(emptyMap())
            for (j in 1..slots) {
                if (elems == 0) break
                val next = mutableListOf<Map<String, ElemRef>>()
                for (p in prev) for (e in 0 until elems) next.add(p + ("V$sort${j - 1}" to ElemRef(sort, e)))
                all.addAll(next)
                prev = next
            }
            return all
        }

        var combos = listOf<Map<String, ElemRef>>(emptyMap())
        for (s in task.sorts) {
            val pres = perSortPrefixes(s.name)
            val next = mutableListOf<Map<String, ElemRef>>()
            for (c in combos) for (p in pres) next.add(c + p)
            combos = next
        }
        return combos.filter { it.isNotEmpty() }.mapIndexed { i, m -> EnvInfo("Env${i + 1}", m) }
    }

    private fun environmentDefs(environments: List<EnvInfo>): String {
        return environments.joinToString("\n        ") { env ->
            val mappingStr = env.mapping.entries.sortedBy { it.key }
                .joinToString(" + ") { (v, e) -> "$v->${e.atom}" }
            "one sig ${env.name} extends Environment {} { mapping = $mappingStr }"
        }
    }


    fun learn(start: Int? = null, stepSize: Int = 2): FOLLearningSolution? {
        val nodesSeq = if (!minimized) {
            listOf(task.maxNumOfNode)
        } else {
            val startNum = start ?: min(max((task.maxNumOfNode - task.sorts.size) / 2, 3), 6)
            val seq = (startNum..task.maxNumOfNode step stepSize).toMutableList()
            if (seq.isEmpty() || seq.last() < task.maxNumOfNode)
                seq.add(task.maxNumOfNode)
            seq
        }

        // Try each split of the variable budget across sorts. Smallest scope first
        // keeps the result minimal; any distribution that separates at that scope wins.
        val usable = usableSorts()
        val distributions = (if (usable.isEmpty()) listOf(emptyMap())
                             else sortDistributions(usable, task.maxQuantifiers))
            // Try splits that use more sorts (and are more balanced) first: real
            // multi-sorted invariants live there, while single-sort splits are usually
            // degenerate. Correctness/minimality is unaffected — every scope is still
            // fully exhausted before moving to the next.
            .sortedWith(
                compareByDescending<Map<String, Int>> { d -> d.values.count { it > 0 } }
                    .thenByDescending { d -> d.values.minOrNull() ?: 0 }
            )

        for (n in nodesSeq) {
            for (dist in distributions) {
                val alloyScript = generateAlloyModel(n, dist)

                val reporter = A4Reporter.NOP
                val world = CompUtil.parseEverything_fromString(reporter, alloyScript)
                val options = alloyOptions()
                val command = world.allCommands.first()
                val t0 = System.currentTimeMillis()
                val solution = TranslateAlloyToKodkod.execute_command(reporter, world.allReachableSigs, command, options)
                val dt = (System.currentTimeMillis() - t0) / 1000.0
                val distStr = dist.entries.joinToString(",") { "${it.key}=${it.value}" }
                System.err.println("[learn] scope=$n dist={$distStr} ${if (solution.satisfiable()) "SAT" else "UNSAT"} in ${dt}s")

                if (solution.satisfiable()) {
                    return FOLLearningSolution(this, world, solution, n, stepSize, task)
                }
            }
        }

        return null
    }
}
