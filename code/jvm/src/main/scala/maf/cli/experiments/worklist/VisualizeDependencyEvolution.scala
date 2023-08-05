package maf.cli.experiments.worklist

import maf.util.Reader
import maf.language.scheme.SchemeParser
import maf.cli.runnables.DynamicWorklistAlgorithms
import maf.cli.runnables.VisualizeTriggers

object VisualizeDependencyEvolution:
    /** Render the given snapshot to a DOT graph */

    def main(args: Array[String]): Unit =
        args.toList match
            case filename :: Nil =>
                val text = Reader.loadFile(filename)
                val program = SchemeParser.parseProgram(text)
                val anl = DynamicWorklistAlgorithms.deprioritizeLargeInflow(0)(program)
                anl.analyze()

                if !anl.finished then println("NOTE: analysis was not finished")
                // iterate over the history of snapshots to visualize the evolution for each of them
                val evolution = anl.snapshots.map(VisualizeTriggers.computeNodes).map(VisualizeTriggers.toDot.tupled)
                // render each individual frame of the evolution ...
                evolution.foreach { input => ??? }

            case _ => println("Usage: COMMAND FILENAME")
