package maf.modular

import maf.core._
import scala.collection.mutable

// A common, but optional extension to ModAnalysis
// Specifically, it keeps track of which components have spawned which other components
trait DependencyTracking[Expr <: Expression] extends ModAnalysis[Expr] { inter =>
    var dependencies: mutable.Map[Component, mutable.Set[Component]] = mutable.Map().withDefaultValue(mutable.Set.empty)
    var readDependencies: Map[Component, Set[Address]] = Map().withDefaultValue(Set.empty)
    var writeEffects: Map[Component, Set[Address]] = Map().withDefaultValue(Set.empty)
    var graph: mutable.Map[Component, mutable.Set[Component]] = mutable.Map()

    def addEdge(src: Component, dest: Component): Unit =
        graph.getOrElseUpdate(src, mutable.Set()) += dest

    def hasEdge(src: Component, dest: Component): Boolean =
        graph.get(src).exists(_.contains(dest))

    def removeEdge(src: Component, dest: Component): Unit =
        graph.get(src).foreach(_.remove(dest))

    def getDirectDeps(src: Component): Set[Component] =
        graph.getOrElse(src, Set.empty).toSet

    def dfs(start: Component, function: Component => Unit): Unit =
        val visited = mutable.Set[Component]()
        val stack = mutable.Stack[Component](start)
        while stack.nonEmpty do
            val node = stack.pop()
            if !visited.contains(node) then
                visited += node
                function(node)
                getDirectDeps(node).foreach(dep => stack.push(dep))

    def bfs(start: Component, function: Component => Unit): Unit =
        val visited = mutable.Set[Component]()
        val queue = mutable.Queue[Component](start)

        while queue.nonEmpty do
            val node = queue.dequeue()
            if !visited.contains(node) then
                visited += node
                function(node)
                getDirectDeps(node).foreach(dep => queue.enqueue(dep))

    def graphToString: String =
        graph.map(from_to => from_to._1.toString + " -> " + from_to._2.map(_.toString).mkString(", ")).mkString("\n")

    // update some rudimentary analysis results
    override def intraAnalysis(component: Component): DependencyTrackingIntra
    trait DependencyTrackingIntra extends IntraAnalysis:
        val visited: Set[Component] = inter.visited
        private def readDeps: Set[Address] =
            R.collect { case r: AddrDependency => r.addr }
        private def writeEffs: Set[Address] =
            W.collect { case w: AddrDependency => w.addr }

        override def commit(): Unit =
            super.commit()
            dependencies += component -> (dependencies(component) ++ C) // update the bookkeeping
            readDependencies += component -> (readDependencies(component) ++ readDeps)
            writeEffects += component -> (writeEffects(component) ++ writeEffs)

    override def configString(): String = super.configString() + "\n  with dependency tracking"

}
