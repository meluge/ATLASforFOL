package cmu.s3d.ltl

data class State(val values: Map<String, Boolean>)

data class LassoTrace(
    val prefix: List<State> = emptyList(),
    val loop: List<State> = emptyList()
) {
    fun length(): Int {
        return prefix.size + loop.size
    }

    fun getTrace(): List<State> {
        return prefix + loop
    }
}