package maf.modular

import maf.core.*
import maf.util.benchmarks.Timeout

/**
 * Keep track of a history of analysis states (called snapshots).
 *
 * A snapshot is captured after each intra analysis and stored in a list called `snapshots` which can be read from client analyses, or can be used by
 * analyses themselves to offer some kind of "rollback" functionality.
 *
 * Note that each snapshot does not necessarily represents the entirety of the analysis state. Therefore it should not be relied upon for complete
 * restore functionality by client analyses. Rather, its purpose is specific to the client analysis used.
 *
 * For example, a client analysis might want to visualize the history of analysis states, or this history might be used by an analysis to make
 * decisions about future abstractions to make or to influence the scheduling of the worklist
 *
 * @tparam E
 *   the type of expression to analyze
 */
trait SnapshotAnalysis[E <: Expression] extends ModAnalysis[E]:
    outer =>

    /** The type of snapshot, must be specified in a concrete subclass, and is requested using the `snapshot` method */
    type Snapshot

    var snapshots: List[Snapshot] = List()

    /** Returns a snapshot of the current analysis state */
    protected def snapshot(): Snapshot

    /** Stores the current analysis state in a history of analysis states */
    private def capture(): Unit =
        snapshots = snapshot() :: snapshots

    trait SnapshotAnalysisIntra extends IntraAnalysis:
        abstract override def analyzeWithTimeout(timeout: Timeout.T): Unit =
            super.analyzeWithTimeout(timeout)
            outer.capture()

    override def intraAnalysis(component: Component): SnapshotAnalysisIntra

case class DependencyTrackingSnapshot[Component](
    /** Call edges */
    calls: Map[Component, Set[Component]],
    /** Read dependencies */
    reads: Map[Component, Set[Address]],
    /** Write edges */
    writes: Map[Component, Set[Address]],
    /** Number of times a dependencies is triggered */
    count: Map[Dependency, Int])

object DependencyTrackingSnapshot:
    def fromAnalysis[E <: Expression](self: DependencyTracking[E]): DependencyTrackingSnapshot[self.Component] =
        DependencyTrackingSnapshot(
          calls = self.dependencies.map { case (k, v) => (k, v.toSet) }.toMap,
          reads = self.readDependencies,
          writes = self.writeEffects,
          count = self.dependencyTriggerCount
        )

trait DependencyTrackingSnapshotAnalysis[E <: Expression] extends DependencyTracking[E], SnapshotAnalysis[E]:
    override def intraAnalysis(component: Component): DependencyTrackingSnapshotIntra

    type Snapshot = DependencyTrackingSnapshot[Component]

    protected def snapshot(): Snapshot =
        DependencyTrackingSnapshot.fromAnalysis(this)

    trait DependencyTrackingSnapshotIntra extends DependencyTrackingIntra, SnapshotAnalysisIntra
