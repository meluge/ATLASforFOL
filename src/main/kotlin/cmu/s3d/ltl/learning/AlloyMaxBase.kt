package cmu.s3d.ltl.learning

import edu.mit.csail.sdg.alloy4.A4Reporter
import edu.mit.csail.sdg.parser.CompUtil
import edu.mit.csail.sdg.translator.A4Options
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod

open class AlloyMaxBase(private val customAlloyOptions: A4Options?) {
    companion object {
        fun defaultAlloyOptions(): A4Options {
            return A4Options().apply {
                solver = A4Options.SatSolver.SAT4JMax
                skolemDepth = 1
                noOverflow = false
                inferPartialInstance = true
            }
        }
    }

    init {
        alloyColdStart()
    }

    protected fun alloyOptions(): A4Options {
        return customAlloyOptions ?: defaultAlloyOptions()
    }

    private fun alloyColdStart() {
        val reporter = A4Reporter.NOP
        val world = CompUtil.parseEverything_fromString(reporter, "")
        val options = defaultAlloyOptions()
        val command = world.allCommands.first()
        TranslateAlloyToKodkod.execute_command(reporter, world.allReachableSigs, command, options)
    }
}