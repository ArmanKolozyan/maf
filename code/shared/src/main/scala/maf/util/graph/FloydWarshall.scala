package maf.util.graph

import cats.kernel.Monoid
import scala.collection.mutable
import scala.reflect.ClassTag
import math.Ordering.Implicits.infixOrderingOps

object FloydWarshall:
    def forallEdges[Node](edges: Iterable[(Node, Set[Node])]): Iterable[(Node, Node)] =
        edges.flatMap { case (from, tos) => tos.map(from -> _) }

    /**
     * Implementation of the Floyd-Warshall algorithm to find the smallest weights for each path between pairs of nodes (i, j) (forall i and j) *
     *
     * @param nodes
     *   the set of nodes in the graph
     * @param edges
     *   the set of edges in the graph
     * @param weights
     *   a mapping from an edge to the weight of that edge
     * @param max
     *   the biggest weight according to Ordering[Weight], such that ∀ a ≠ max, a < max
     * @return
     *   a matrix of shortest weights for a node i in the rows and node j in the columns
     */
    def floydwarshall[Node, Weight: Monoid: ClassTag: Ordering](
        nodes: Set[Node],
        edges: Map[Node, Set[Node]],
        weights: Map[(Node, Node), Weight],
        max: Weight
      ): Map[(Node, Node), Weight] =
        val dist: mutable.Map[(Node, Node), Weight] = mutable.Map().withDefaultValue(max)
        // initialize direct edges
        forallEdges(edges).foreach { case edge @ (from, to) => dist((from, to)) = weights(edge) }
        // Initialize self-distances to zero
        nodes.foreach(node => dist((node, node)) = Monoid[Weight].empty)
        // the loops
        for
            k <- nodes
            i <- nodes
            j <- nodes
        do if dist((i, j)) > Monoid[Weight].combine(dist((i, k)), dist(k, j)) then dist((i, j)) = Monoid[Weight].combine(dist((i, k)), dist(k, j))
        // return the result
        dist.toMap
