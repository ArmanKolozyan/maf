package maf.cli.experiments.worklist

import maf.util.Reader
import maf.language.scheme.SchemeParser
import maf.cli.runnables.DynamicWorklistAlgorithms
import maf.cli.runnables.VisualizeTriggers
import scala.sys.process.*
import java.io.ByteArrayInputStream

object VisualizeDependencyEvolution:
    /** Render the given snapshot to a DOT graph */

    def main(args: Array[String]): Unit =
        args.toList match
            case filename :: Nil =>
                val text = Reader.loadFile(filename)
                println("File loaded")
                val program = SchemeParser.parseProgram(text)
                val anl = DynamicWorklistAlgorithms.deprioritizeLargeInflow(0)(program)
                anl.analyze()
                println("Analysis finished")

                if !anl.finished then println("NOTE: analysis was not finished")
                // iterate over the history of snapshots to visualize the evolution for each of them
                val evolution = anl.snapshots.reverse
                    .take(400)
                    .zipWithIndex
                    .map { case (snapshot, idx) =>
                        println(s"iteration $idx")
                        VisualizeTriggers.computeNodes(snapshot)
                    }
                    .map(VisualizeTriggers.toDot.tupled)
                println("Evolution computed")
                // render each individual frame of the evolution ...
                evolution.zipWithIndex.foreach { case (input, i) =>
                    ((s"sfdp -x -Goverlap=scale -Tpdf -o /tmp/frame-$i.pdf") #< ByteArrayInputStream(input.getBytes())).!!
                }

            case _ => println("Usage: COMMAND FILENAME")
