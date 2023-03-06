package maf.cli.runnables

import maf.core.Expression
import maf.language.scheme.{SchemeExp, SchemeParser}
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf.{SchemeModFComponent, SchemeModFKCallSiteSensitivity, SchemeModFNoSensitivity, SimpleSchemeModFAnalysis}
import maf.modular.{Dependency, DependencyTracking, ModAnalysis}
import maf.modular.worklist.{PriorityQueueWorklistAlgorithm, RandomWorklistAlgorithm}
import maf.util.Reader
import maf.util.benchmarks.Timer

object DynamicWorklistAlgorithms extends App:

  trait MostDependenciesFirstWorklistAlgorithm[Expr <: Expression] extends PriorityQueueWorklistAlgorithm[Expr] :
    var depCount: Map[Component, Int] = Map.empty.withDefaultValue(0)
    val ordering: Ordering[Component] = Ordering.by(depCount)
    var correctDependencies: Map[Component, Set[Component]] = Map().withDefaultValue(Set.empty)

    override def updateDependencies(dependencies: Map[Component, Set[Component]]): Unit =
      dependencies.keySet.foreach(comp => {
        val dependencies = getDependencies(comp)
        depCount += (comp -> dependencies.size)
      }
    )

    def getDependencies(cmp: Component): Set[Component] = {
      correctDependencies.getOrElse(cmp, Set.empty)
    }


  def runAnalysis[A <: ModAnalysis[SchemeExp] with DependencyTracking[SchemeExp]](bench: (String, SchemeExp), analysis: SchemeExp => A): Map[A#Component, Set[A#Component]] =
    val a: A = analysis(bench._2)
    a.analyze()
    val dependencies: Map[A#Component, Set[A#Component]] = a.dependencies
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
        val analysis: ModAnalysis[SchemeExp] with MostDependenciesFirstWorklistAlgorithm[SchemeExp] = depAnalysis(program)
        val dependencies: Map[analysis.Component, Set[analysis.Component]] = runAnalysis((b._2, program), program => randomAnalysis(program))
        analysis.correctDependencies = dependencies})
