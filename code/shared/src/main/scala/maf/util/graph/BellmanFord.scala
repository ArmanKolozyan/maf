package maf.util.graph

import scala.collection.mutable
import scala.reflect.ClassTag
import cats.kernel.Monoid
import math.Ordering.Implicits.infixOrderingOps

// BASED ON: https://www.geeksforgeeks.org/detect-negative-cycle-graph-bellman-ford/
object BellmanFord:
    private def isThisCycleNegative[Node, Weight: Monoid : ClassTag : Ordering](        nodes: Set[Node],
                                                                                  edges: Map[Node, Set[Node]],
                                                                                  weights: Map[(Node, Node), Weight],
                                                                                  src: Node, // Use integer index
                                                                                  dist: mutable.Map[Node, Weight],
                                                                                  max: Weight

                                                                             ): Boolean = {
        // Step 1: Initialize distances from src
        // to all other vertices as max
        for (node <- nodes) {
            dist(node) = max
        }

        dist(src) = Monoid[Weight].empty

        // Step 2: Relax all edges |V| - 1 times.
        for (_ <- 1 until nodes.size) {
            for (node <- nodes; neighbor <- edges.getOrElse(node, Set.empty)) {
                val weight = weights.getOrElse((node, neighbor), max)
                if dist(node) != max && Monoid[Weight].combine(dist(node), weight) < dist(neighbor) then {
                    dist(neighbor) = Monoid[Weight].combine(dist(node), weight)
                }
            }
        }

        // Step 3: check for negative-weight cycles.
        for (node <- nodes; neighbor <- edges.getOrElse(node, Set.empty)) {
            val weight = weights.getOrElse((node, neighbor), max)
            if dist(node) != max && Monoid[Weight].combine(dist(node), weight) < dist(neighbor) then {
                return true
            }
        }

        false
    }

    /**
     * Checks if given graph has negative weight cycles.
     */
    def hasNegativeCycle[Node, Weight: Monoid : ClassTag : Ordering](
                                                                                   nodes: Set[Node],
                                                                                   edges: Map[Node, Set[Node]],
                                                                                   weights: Map[(Node, Node), Weight],
                                                                                   max: Weight
                                                                               ): Boolean = {

        val visited: mutable.Map[Node, Boolean] = mutable.Map().withDefaultValue(false)
        val dist: mutable.Map[Node, Weight] = mutable.Map().withDefaultValue(max)

        // Call Bellman-Ford for all those vertices
        // that are not visited
        for (node <- nodes) {
            if !visited(node) then {
                // If cycle found, return
                if isThisCycleNegative(nodes, edges, weights, node, dist, max) then
                    return true

                // Otherwise, mark all vertices that are visited
                // in above call.
                for (node <- nodes) {
                    if dist(node) != max then
                        visited(node) = true
                }
            }
        }

        false
    }
