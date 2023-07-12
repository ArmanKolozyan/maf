package maf.cli.runnables

import maf.core.*
import maf.language.scheme.*
import maf.cli.experiments.worklist.ProgramGenerator
import maf.cli.runnables.AnalyzeWorklistAlgorithms.FIFOanalysis
import maf.cli.runnables.AnalyzeWorklistAlgorithms.LIFOanalysis
import maf.util.MapUtil.invert
import maf.modular.Dependency

/**
 * Utility to visualize the dependency graph using GraphViz.
 *
 * Each edge represents a dependency and its direction the flow of values. The thickness of an edge represents how many times the dependency has been
 * triggered.object
 */
object VisualizeTriggers:
    import DynamicWorklistAlgorithms.*

    type Exp = SchemeExp

    private val programText: String = ProgramGenerator.upflow2(10)

    private val analyses: Map[String, (Exp) => DynamicWorklistAlgorithms.Analysis] = Map(
      "FIFO" -> FIFOanalysis(theK = 0),
      "LIFO" -> LIFOanalysis(theK = 0)
    )

    private def toDot(nodes: Map[String, Set[String]], count: Map[Dependency, Int]): Unit = ???

    def main(args: Array[String]): Unit =
        if args.size < 1 then
            println("USAGE: maf ANALYSIS")
            System.exit(1)
        else
            // selected the appropriate analysis
            val selected = analyses(args(0))
            // parse the program
            val program = SchemeParser.parseProgram(programText)
            // construct the analysis
            val anl = selected(program)
            // run the analysis
            anl.analyze()
            println("Analysis completed... Constructing graph.")
            val reads: Map[String, Set[String]] = anl.readDependencies.invert.map { case (k, v) => (k.toString, v.map(_.toString)) }.toMap
            val wrts: Map[String, Set[String]] = anl.writeEffects.map { case (k, v) => (k.toString, v.map(_.toString)) }.toMap
            toDot(reads ++ wrts, anl.dependencyTriggerCount)
