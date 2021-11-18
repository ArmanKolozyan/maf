package maf.cli.runnables

import maf.aam.*
import maf.aam.scheme.*
import maf.language.scheme.*
import maf.language.scheme.primitives.*
import maf.modular.scheme.*
import maf.util.*
import maf.util.graph.*
import maf.util.benchmarks.Timeout
import scala.concurrent.duration._
import scala.io.StdIn
import maf.util.benchmarks.Timer

object AAMTester:
    private def analysis(b: SchemeExp): SchemeAAMSemantics =
      new SchemeAAMSemantics(b)
        with AAMAnalysis
        with SchemeAAMAnalysisResults
        with SchemeAAMContextInsensitivity
        with SchemeConstantPropagationDomain
        with SchemeAAMNoExt

    private def parseProgram(txt: String): SchemeExp =
        val parsed = SchemeParser.parse(txt)
        val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
        val transf = SchemeMutableVarBoxer.transform(prelud)
        SchemeParser.undefine(transf)

    /**
     * Run the program
     * @param name
     *   the name of the program to analyze
     */
    def run(name: String): Unit =
        val content = Reader.loadFile(name)
        val program = parseProgram(content)
        val graph = new DotGraph[GraphElementAAM, GraphElement]()
        given gInst: Graph[graph.G, GraphElementAAM, GraphElement] = graph.G.typeclass
        val theAnalysis = analysis(program)

        def findState(states: Set[theAnalysis.State], g: graph.G, id: String): Option[theAnalysis.State] =
            val stateId = id.toIntOption
            if stateId.isEmpty then None
            else
                val state = gInst.findNodeById(g, stateId.get)
                state match
                    case Some(state) =>
                      states.find(state.hsh == _.hashCode)
                    case None => None

        val (time, (states, g)) = Timer.time {
          theAnalysis.analyzeWithTimeout(Timeout.start(Duration(12, SECONDS)), graph.G.typeclass.empty)
        }

        g.toFile(name.replace("/", "_").nn + ".dot")
        if theAnalysis.finished then
            println(s"Analysis finished in ${time / (1000 * 1000)} milliseconds, by visiting ${states.size} states")
            println(s"Set of answsers ${states.filter(theAnalysis.isFinal(_)).flatMap(theAnalysis.extractValue(_))}")
        else println(s"The analysis timed-out in ${time / (1000 * 1000)} millisconds")

        print("query>>> ")
        var input = StdIn.readLine()

        while (input != ":q") do
            println(input.nn.split('.').nn.mkString("::"))
            val parts = input.split('.').nn.flatMap(s => findState(states, g, s.nn))
            for window <- parts.sliding(2, 1) do
                println("== New comparison ==")
                window.foreach(state => theAnalysis.printDebug(state, true))
                if window.size == 2 then theAnalysis.compareStates(window(0), window(1))

            print("query>>> ")
            input = StdIn.readLine()

    def main(args: Array[String]): Unit =
      if args.size > 0 then run(args(0)) else println("Please provide a file")