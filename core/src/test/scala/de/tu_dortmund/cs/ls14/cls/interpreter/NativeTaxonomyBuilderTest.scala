package de.tu_dortmund.cs.ls14.cls.interpreter

import org.scalatest.FunSpec

class NativeTaxonomyBuilderTest extends FunSpec {
  trait Super
  class SubA extends Super
  class SubB extends Super

  type AliasSubA = SubA

  val superTypeName = ReflectedRepository.nativeTypeOf[Super].name
  val subATypeName = ReflectedRepository.nativeTypeOf[SubA].name
  val subBTypeName = ReflectedRepository.nativeTypeOf[SubB].name
  val aliasSubATypeName = ReflectedRepository.nativeTypeOf[AliasSubA].name
  val stringTypeName = ReflectedRepository.nativeTypeOf[String].name

  val seqStringTypeName = ReflectedRepository.nativeTypeOf[Seq[String]].name
  val seqSuperTypeName = ReflectedRepository.nativeTypeOf[Seq[Super]].name
  val seqSubATypeName = ReflectedRepository.nativeTypeOf[Seq[SubA]].name

  val taxonomy =
    new NativeTaxonomyBuilder()
      .addNativeType[Super]
      .addNativeType[SubA]
      .addNativeType[SubB]
      .addNativeType[AliasSubA]
      .addNativeType[String]
      .addNativeType[Seq[String]]
      .addNativeType[Seq[Super]]
      .addNativeType[Seq[SubA]]
      .taxonomy

  describe(taxonomy.underlyingMap.toString()) {
    describe("when asked for subtypes of Super") {
      it("should include SubA") {
        assert(taxonomy(superTypeName).contains(subATypeName))
      }
      it("should include SubB") {
        assert(taxonomy(superTypeName).contains(subBTypeName))
      }
      it("should include AliasSubA") {
        assert(taxonomy(superTypeName).contains(aliasSubATypeName))
      }
      it("should not include String") {
        assert(!taxonomy(superTypeName).contains(stringTypeName))
      }
    }
    describe("when asked for subtypes of another type") {
      it("should not include entries for String") {
        assert(taxonomy(stringTypeName).isEmpty)
      }
      it("should not include entries for SubB") {
        assert(taxonomy(subBTypeName).isEmpty)
      }
      it("should include reflexivity of SubA and AliasSubA") {
        assert(taxonomy(subATypeName).contains(aliasSubATypeName))
        assert(taxonomy(aliasSubATypeName).contains(subATypeName))
      }
    }
    describe("When asked for sequences") {
      it("should respect covariance") {
        assert(taxonomy(seqSuperTypeName).contains(seqSubATypeName))
      }
      it("should not introduce unrelated subtypes") {
        assert(taxonomy(seqStringTypeName).isEmpty)
        assert(!taxonomy(seqSuperTypeName).contains(seqStringTypeName))
      }
    }
  }
}