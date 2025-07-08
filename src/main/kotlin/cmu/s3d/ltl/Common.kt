package cmu.s3d.fol

data class FOLSort(val name: String)

data class FOLRelation(
    val name: String,
    val signature: List<String>  // List of sort names
) {
    val arity: Int get() = signature.size
}

data class FOLFunction(
    val name: String,
    val signature: List<String>  // Input sorts + output sort
) {
    val arity: Int get() = signature.size
}

data class FOLConstant(
    val name: String,
    val sort: String
)

data class FOLStructure(
    val constants: List<FOLConstant>,
    val relationFacts: Map<String, List<List<String>>>,  // relation -> list of tuples
    val functionFacts: Map<String, List<List<String>>> = emptyMap()  // function -> list of tuples
)

data class FOLExample(
    val structure: FOLStructure,
    val isPositive: Boolean
)