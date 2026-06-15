package cmu.s3d.fol.learning

import cmu.s3d.fol.FOLStructure

/**
 * A minimal first-order formula AST plus a native evaluator over finite structures.
 *
 * This is deliberately independent of Alloy/Kodkod: it re-checks, from scratch, that
 * a synthesized separator actually accepts every positive example and rejects every
 * negative one. It is a correctness oracle for the Alloy encoding — if the solver says
 * "separator" but this disagrees, the encoding (not the solver) is wrong.
 */
sealed class Fml
data class QForall(val v: String, val sort: String, val body: Fml) : Fml()
data class QExists(val v: String, val sort: String, val body: Fml) : Fml()
data class FNot(val c: Fml) : Fml()
data class FAnd(val l: Fml, val r: Fml) : Fml()
data class FOr(val l: Fml, val r: Fml) : Fml()
data class FImplies(val l: Fml, val r: Fml) : Fml()
/** rel applied to variable keys (e.g. "edge", ["Vnode0","Vnode1"]). */
data class FAtom(val rel: String, val vars: List<String>) : Fml()

object SeparationChecker {

    /** Evaluate a closed formula on a structure under the given (var-key -> constant-name) env. */
    fun eval(f: Fml, s: FOLStructure, env: Map<String, String>): Boolean = when (f) {
        is FNot -> !eval(f.c, s, env)
        is FAnd -> eval(f.l, s, env) && eval(f.r, s, env)
        is FOr -> eval(f.l, s, env) || eval(f.r, s, env)
        is FImplies -> !eval(f.l, s, env) || eval(f.r, s, env)
        is QForall -> s.constants.filter { it.sort == f.sort }
            .all { c -> eval(f.body, s, env + (f.v to c.name)) }
        is QExists -> s.constants.filter { it.sort == f.sort }
            .any { c -> eval(f.body, s, env + (f.v to c.name)) }
        is FAtom -> {
            val args = f.vars.map { env[it] }
            if (args.any { it == null }) false
            else (s.relationFacts[f.rel] ?: emptyList()).any { it == args }
        }
    }

    data class Result(val ok: Boolean, val failingPositives: List<Int>, val failingNegatives: List<Int>) {
        fun report(): String =
            if (ok) "CHECK: PASS — separator accepts all positives and rejects all negatives"
            else "CHECK: FAIL — misclassified positive examples=$failingPositives, negative examples=$failingNegatives"
    }

    /** A formula separates iff it holds on every positive and on no negative. */
    fun check(f: Fml, task: FOLTask): Result {
        val badPos = task.positiveExamples.indices.filter { !eval(f, task.positiveExamples[it].structure, emptyMap()) }
        val badNeg = task.negativeExamples.indices.filter { eval(f, task.negativeExamples[it].structure, emptyMap()) }
        return Result(badPos.isEmpty() && badNeg.isEmpty(), badPos, badNeg)
    }
}
