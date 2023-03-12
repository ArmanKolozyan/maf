package maf.cli.runnables

import maf.core.Expression
import maf.language.scheme.{SchemeExp, SchemeParser}
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf.{SchemeModFComponent, SchemeModFKCallSiteSensitivity, SchemeModFNoSensitivity, SimpleSchemeModFAnalysis, StandardSchemeModFComponents}
import maf.modular.{Dependency, DependencyTracking, ModAnalysis}
import maf.modular.worklist.{PriorityQueueWorklistAlgorithm, RandomWorklistAlgorithm}
import maf.util.Reader
import maf.util.benchmarks.Timer

object DynamicWorklistAlgorithms extends App:

  trait MostDependenciesFirstWorklistAlgorithm[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    lazy val ordering: Ordering[Component] = Ordering.by(comp => depCount(comp))
    private var correctDependencies: Map[Component, Set[Component]] = Map().withDefaultValue(Set.empty)

    def updateDependencies(dependencies: Map[Component, Set[Component]]): Unit =
      correctDependencies = dependencies
      dependencies.keySet.foreach(comp => {
        val currDep = dependencies.getOrElse(comp, Set.empty)
        depCount += (comp -> currDep.size)
      }
    )




  type Deps = Map[SchemeModFComponent, Set[SchemeModFComponent]]
  type SchemeAnalysisWithDeps = ModAnalysis[SchemeExp] with DependencyTracking[SchemeExp] with StandardSchemeModFComponents

  def runAnalysis[A <: SchemeAnalysisWithDeps] (bench: (String, SchemeExp), analysis: SchemeExp => A): Deps =
    val a: A = analysis(bench._2)
    a.analyze()
    val dependencies = a.dependencies
    println(dependencies)
    dependencies

  def randomAnalysis(program: SchemeExp) =
    new SimpleSchemeModFAnalysis(program)
      with SchemeModFNoSensitivity
      with SchemeConstantPropagationDomain
      with DependencyTracking[SchemeExp]
      with RandomWorklistAlgorithm[SchemeExp] {
      override def intraAnalysis(cmp: SchemeModFComponent) =
        new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
    }

  def depAnalysis(program: SchemeExp) =
    new SimpleSchemeModFAnalysis(program)
      with SchemeModFNoSensitivity
      with SchemeConstantPropagationDomain
      with DependencyTracking[SchemeExp]
      with MostDependenciesFirstWorklistAlgorithm[SchemeExp] {
      override def intraAnalysis(cmp: SchemeModFComponent) =
        new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
    }

  val bench: Map[String, String] = List(
        ("test/R5RS/icp/icp_2_aeval.scm", "aeval"),
      ).toMap

  bench.foreach({ b =>
        val program = SchemeParser.parseProgram(Reader.loadFile(b._1)) // doing parsing only once
        val analysis = depAnalysis(program)
        val dependencies = runAnalysis((b._2, program), program => randomAnalysis(program))
        analysis.updateDependencies(dependencies)})
