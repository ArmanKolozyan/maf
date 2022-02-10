package maf.test.language.ContractScheme

/** A generator that generates random input regardless of the contract and topLevelFunction parameter */
class PurelyRandomGenerator(primitives: List[String]) extends RandomInputGenerator:
    private val generator: ConcreteGenerators = ConcreteGenerators(primitives)
    override def generateInput(contract: Set[String] = Set(), topLevelFunction: Option[String] = None): ConcreteValues.Value = generator.any
