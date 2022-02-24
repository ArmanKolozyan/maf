package maf.cli.runnables

import maf.bench.scheme.SchemeBenchmarkPrograms
import maf.cli.experiments.incremental.SplitPerformance
import maf.language.CScheme.*
import maf.language.change.CodeVersion.*
import maf.language.scheme.SchemeExp
import maf.language.scheme.interpreter.{ProgramError, SchemeInterpreter}
import maf.language.scheme.primitives.SchemePrelude
import maf.modular.{GlobalStore, ModAnalysis}
import maf.modular.incremental.IncrementalConfiguration.*
import maf.modular.scheme.modf.*
import maf.modular.incremental.{IncrementalLogging, IncrementalModAnalysis, *}
import maf.modular.incremental.scheme.IncrementalSchemeAnalysisInstantiations.*
import maf.modular.incremental.ProgramVersionExtracter.*
import maf.modular.incremental.scheme.lattice.*
import maf.modular.incremental.scheme.modf.IncrementalSchemeModFBigStepSemantics
import maf.modular.scheme.{PrmAddr, SchemeTypeDomain}
import maf.modular.worklist.LIFOWorklistAlgorithm
import maf.util.{Reader, Writer}
import maf.util.Writer.Writer
import maf.util.benchmarks.{Timeout, Timer}
import maf.util.graph.DotGraph
import maf.util.graph.DotGraph.*

import scala.concurrent.duration.*

object IncrementalRun extends App:

    def newAnalysis(text: SchemeExp, configuration: IncrementalConfiguration) =
      new IncrementalSchemeModFAnalysisTypeLattice(text, configuration)
        with IncrementalLogging[SchemeExp]
        //with IncrementalDataFlowVisualisation[SchemeExp]
        {
        override def focus(a: Addr): Boolean = false //a.toString.toLowerCase().nn.contains("ret")

        override def intraAnalysis(cmp: SchemeModFComponent) = new IntraAnalysis(cmp)
          with IncrementalSchemeModFBigStepIntra
          with IncrementalGlobalStoreIntraAnalysis
          //  with AssertionModFIntra
          with IncrementalLoggingIntra
        //with IncrementalVisualIntra
      }

    // Performance benchmarks
    def perfAnalysis(e: SchemeExp, config: IncrementalConfiguration) = new IncrementalSchemeModFAnalysisTypeLattice(e, config)
      with SplitPerformance[SchemeExp]
      with IncrementalLogging[SchemeExp] {
      mode = Mode.Coarse
      var cnt = 0
      override def run(timeout: Timeout.T) =
        super.run(timeout)
        println(cnt)
      override def intraAnalysis(cmp: Component) =
        new IntraAnalysis(cmp)
          with IncrementalSchemeModFBigStepIntra
          with IncrementalGlobalStoreIntraAnalysis
          with SplitPerformanceIntra
          with IncrementalLoggingIntra
        {
          override def analyzeWithTimeout(timeout: Timeout.T): Unit =
            cnt = cnt + 1
            super.analyzeWithTimeout(timeout)
        }
    }

    // Analysis from soundness tests.
    def base(program: SchemeExp) = new ModAnalysis[SchemeExp](program)
      with StandardSchemeModFComponents
      with SchemeModFNoSensitivity
      with SchemeModFSemanticsM
      with LIFOWorklistAlgorithm[SchemeExp]
      with IncrementalSchemeModFBigStepSemantics
      with IncrementalSchemeTypeDomain // IncrementalSchemeConstantPropagationDomain
      with IncrementalGlobalStore[SchemeExp]
      with IncrementalLogging[SchemeExp]
      //with IncrementalDataFlowVisualisation[SchemeExp]
      {
      override def focus(a: Addr): Boolean = false // a.toString.contains("VarAddr(n")
      var configuration: IncrementalConfiguration = ci
      mode = Mode.Fine
      override def intraAnalysis(
          cmp: Component
        ) = new IntraAnalysis(cmp) with IncrementalSchemeModFBigStepIntra with IncrementalGlobalStoreIntraAnalysis with IncrementalLoggingIntra
      //with IncrementalVisualIntra
    }

    def compareAnalyses(inc: IncrementalSchemeModFAnalysisTypeLattice, rean: IncrementalSchemeModFAnalysisTypeLattice): Unit =
      val cName = inc.configuration.toString
      // Both analyses normally share the same lattice, allocation schemes,... which makes it unnecessary to convert values etc.
      val iStore = inc.store.withDefaultValue(inc.lattice.bottom)
      val rStore = rean.store.withDefaultValue(rean.lattice.bottom)

      val allAddr = iStore.keySet ++ rStore.keySet
      var e: Long = 0L
      var l: Long = 0L
      var m: Long = 0L
      allAddr.foreach({ a =>
        val incr = iStore(a)
        val rean = rStore(a)
        if incr == rean then e += 1 // Both results are the same => equally precise.
        else if inc.lattice.subsumes(incr, rean.asInstanceOf[inc.Value]) then l += 1 // The incremental value subsumes the value of the full reanalysis => less precise.
        else {
          //System.err.nn.println(s"$a: $incr < $rean") // Soundness error.
          //System.err.nn.flush()
          m += 1 // The incremental value is subsumed by the value of the full reanalysis => more precise.
        }
      })
      System.err.nn.println(s"less precise: $l -- equal: $e -- more precise: $m")
    end compareAnalyses

    // Runs the program with a concrete interpreter, just to check whether it makes sense (i.e., if the concrete interpreter does not error).
    // Useful when reducing a program when debugging the analysis.
    def interpretProgram(file: String): Unit =
        val prog = CSchemeParser.parseProgram(Reader.loadFile(file))
        val i = new SchemeInterpreter((_, _) => (), stack = true)
        List(Old, New).foreach { version =>
          try
            print("*")
            i.run(prog, Timeout.start(Duration(3, MINUTES)), version)
          catch {
            case ProgramError(e) => System.err.nn.println(e)
          }
        }
        println("Done interpreting.")

    val modFbenchmarks: List[String] = List(
      "test/changes/scheme/slip-0-to-1.scm"
    )

    def newTimeout(): Timeout.T = Timeout.start(Duration(20, MINUTES))

    modFbenchmarks.foreach { bench =>
      try {
        println(s"***** $bench *****")
        //interpretProgram(bench)
        val text = CSchemeParser.parseProgram(Reader.loadFile(bench))

        val a = newAnalysis(text, ci_di_wi)
        a.analyzeWithTimeout(newTimeout())
        assert(a.finished)

        val noOpt = a.deepCopy()
        noOpt.configuration = noOptimisations
        noOpt.updateAnalysis(newTimeout())
        assert(noOpt.finished)

        val cidiwi = a.deepCopy()
        cidiwi.configuration = ci_di_wi
        cidiwi.updateAnalysis(newTimeout())
        assert(cidiwi.finished)

        compareAnalyses(cidiwi, noOpt)

      } catch {
        case e: Exception =>
          e.printStackTrace(System.out)
      }
    }

    println("Done")
end IncrementalRun

// Prints the maximal heap size.
object Memorycheck extends App:
    def formatSize(v: Long): String =
        if v < 1024 then return s"$v B"
        val z = (63 - java.lang.Long.numberOfLeadingZeros(v)) / 10
        s"${v.toDouble / (1L << (z * 10))} ${" KMGTPE".charAt(z)}B"

    println(formatSize(Runtime.getRuntime.nn.maxMemory()))

object IncrementalExtraction extends App:

    val text: String = "test/changes/scheme/generated/R5RS_icp_icp_1c_ontleed-4.scm"
    val version: Version = New

    val program = CSchemeParser.parseProgram(Reader.loadFile(text))
    println((if version == New then ProgramVersionExtracter.getUpdated(program) else ProgramVersionExtracter.getInitial(program)).prettyString())
