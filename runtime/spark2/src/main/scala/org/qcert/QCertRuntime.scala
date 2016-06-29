/*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.qcert

import java.util.Comparator

import com.google.gson.{JsonElement, JsonNull, JsonObject, JsonPrimitive}
import org.apache.spark.sql.catalyst.expressions.GenericRowWithSchema
import org.apache.spark.sql.types._
import org.apache.spark.sql.{Dataset, Row, SparkSession}
import org.apache.spark.{SparkConf, SparkContext}

object test extends QCertRuntime {

  def castToCustomerAndUnbrand(r: Row): Either = {
    if (r.getSeq[String](r.fieldIndex("$type")).contains("entities.Customer")) {
      val blob = r.getAs[Row]("$data").getAs[String]("$blob")
      left(fromBlob(wrappedCustomerType, blob).asInstanceOf[Row])
    } else {
      right(srow(StructType(Seq())))
    }
  }

  override def run(world: Dataset[Either]): Unit = {
    val f = world.first()
    val bar = cast(f, wrappedCustomerType, "entities.Customer")
    println(bar)

    val foo = world.collect().map((world_element: Row) => {
      either(cast(world_element, wrappedCustomerType, "entities.Customer")/* castToCustomerAndUnbrand(world_element) */,
        (customer: Row) => {
          println(customer)
          dot[String]("name")(unbrand(customer))
          // val blob = customer.getAs[Row]("$data").getAs[String]("$blob")
          // println(blob)
          // println(fromBlob(customerType, blob))
        },
        (not_a_customer: Row) => {
          "bla"
        })
    })
    foo foreach((n: String) => println(n))
  }
}

abstract class QCertRuntime {
  // TODO revisit naming -- we don't want to clash with spark.sql.functions._ functions

  def customerType =
    StructType(Seq(
      StructField("age", IntegerType),
      StructField("cid", IntegerType),
      StructField("name", StringType)))

  def wrappedCustomerType =
    StructType(Seq(
      StructField("$blob", StringType),
      StructField("$known", customerType)))

  def purchaseType =
    StructType(
      StructField("cid", IntegerType)::
      StructField("name", StringType)::
      StructField("pid", IntegerType)::
      StructField("quantity", IntegerType)::Nil)

  def mainEntityType =
    StructType(
      StructField("doubleAttribute", DoubleType)::
      StructField("id", IntegerType)::
      StructField("stringId", StringType)::Nil)

  def test07InputType =
    StructType(
      StructField("$type", ArrayType(StringType))::
      StructField("$data", StructType(
        StructField("$known", StructType(Nil))::
        StructField("$blob", StringType)::Nil
      ))::Nil
    )

  val CONST$WORLD_07 = Nil

  val CONST$WORLD = CONST$WORLD_07

  def run(world: Dataset[Row])

  def main(args: Array[String]): Unit = {
    val sparkCtx = new SparkContext("local", "Test 07", new SparkConf())
    sparkCtx.setLogLevel("ERROR")
    val session = SparkSession.builder().getOrCreate()

    val jsonFile = "/Users/stefanfehrenbach/global-rules/docs/notes/test07-sparkio.json"
    val df0 = session.read.schema(test07InputType).json(jsonFile)
    //printing some debugging output for sanity-checking
    System.out.println("--- input schema ---")
    df0.printSchema()
    System.out.println("--- input documents ---")
    df0.show()

    run(df0)
    sparkCtx.stop()
  }

    /* Data
     * ====
     *
     * Int, Double, String, Boolean
     * Records are Rows with schema with fields in lexicographic order.
     * Bags are arrays, unordered. TODO change this!
     * Either and Branded values are encoded as Rows.
     */

  def fromBlob(t: DataType, b: JsonElement): Any = t match {
    case t: IntegerType => b.getAsInt
    case t: BooleanType => b.getAsBoolean
    case t: StringType => b.getAsString
    case t: ArrayType => {
      import scala.collection.JavaConverters._
      b.getAsJsonArray.iterator().asScala.map((e: JsonElement) => fromBlob(t.elementType, e)).toArray
    }
    case t: StructType => t.fieldNames match {
      case Array("$left", "$right") => sys.error("either")
      case Array("$type", "$data") => sys.error("brand")
      case Array("$blob", "$known") =>
        val r = b.getAsJsonObject
        val knownFieldValues = t("$known").dataType.asInstanceOf[StructType].fields map ((field: StructField) => {
          fromBlob(field.dataType, r.get(field.name))
        })
        srow(t,
          // We have the full record in the blob field, even for closed records // TODO change?
          r.toString,
          srow(t("$known").dataType.asInstanceOf[StructType], knownFieldValues:_*))
      case _ =>
        srow(t, t.fields.map((field) => fromBlob(field.dataType, b.getAsJsonObject.get(field.name))):_*)
    }
  }

  def fromBlob(t: DataType, b: String): Any =
    fromBlob(t, new com.google.gson.JsonParser().parse(b))

  /* Records
 * =======
 *
 * We represent records as Rows with a schema of StructType.
 * Rows are glorified tuples. We can access fields by name, but most operations are by position only.
 * Fields must be ordered by field name!
 */
  // This seems to cause trouble, because scala can't find an ordering, or something.
  // This might allow us to override the default ordering for Rows, maybe.
  // type Record = Row

  /** More convenient record (row with schema) construction.
    * Splice array into varargs call: let a = Array(1, 2); srow(schema, a:_*) */
  def srow(s: StructType, vals: Any*): Row = {
    assert(s.fields.length == vals.length,
      "Number of record fields does not match the schema. Did you forget to splice an array parameter?")
    assert(s.fieldNames.sorted.distinct.sameElements(s.fieldNames),
      "Field names must be unique and sorted!")
    new GenericRowWithSchema(vals.toArray, s)
  }

  // TODO this is a mess
  def recordConcat(l: Row, r: Row): Row = {
    val rightFieldNames = r.schema.fieldNames diff l.schema.fieldNames
    val rightFieldNamesSet = rightFieldNames.toSet
    val allFieldNames = (rightFieldNames ++ l.schema.fieldNames).distinct.sorted
    val schema = allFieldNames.foldLeft(new StructType())((schema: StructType, field: String) => {
      val inLeft = l.schema.fieldNames.indexOf(field)
      schema.add(if (inLeft == -1) r.schema.fields(r.schema.fieldNames.indexOf(field)) else l.schema.fields(inLeft))
    })
    // val schema: StructType = rightFieldNames.foldLeft(l.schema)((schema: StructType, rfn: String) =>
    //  schema.add(r.schema.fields(r.fieldIndex(rfn))))
    val names = l.schema.fieldNames ++ rightFieldNames
    val values = l.toSeq ++ rightFieldNames.map((rfn: String) => r.get(r.fieldIndex(rfn)))
    val sortedValues = (names zip values).sortBy(_._1).map(_._2)
    srow(schema, sortedValues: _*)
  }

  def dot[T](n: String)(l: Row): T =
    l.getAs[Row]("$known").getAs[T](n)

  def mergeConcat(l: Row, r: Row): Array[Row] = {
    val concatenated = recordConcat(l, r)
    val duplicates = l.schema.fieldNames intersect r.schema.fieldNames
    // TODO could do this before...
    for (field <- duplicates)
      if (!equal(r.get(r.fieldIndex(field)), concatenated.get(concatenated.fieldIndex(field))))
        return Array()
    Array(concatenated)
  }

  /** UnaryOp ARec */
  def singletonRecord(n: String, v: Int): Row = {
    srow(StructType(StructField(n, IntegerType, false) :: Nil), v)
  }

  def singletonRecord(n: String, v: Row): Row = {
    srow(StructType(StructField(n, v.schema, false) :: Nil), v)
  }

  // TODO Ugh, this hacky inference business works for primitives and even records, but not Arrays
  //  def singltonRecord[T](n: String, v: Array[T]): Record = {
  //    srow(StructType(StructField(n, ArrayType(T), false)::Nil), v)
  //  }

  /* Either
 * ======
 *
 * Encode either as a record with left and right fields. Unlike in the Java/JS harness,
 * we need both fields to be actually present, because Rows are really indexed by position.
 * If we had only one field named left or right, we could not make a collection of eithers.
 */
  // Could we use Scala's either through a user-defined datatype or something?
  type Either = Row

  def eitherStructType(l: DataType, r: DataType): StructType =
    StructType(StructField("$left", l, true) :: StructField("$right", r, true) :: Nil)

  // Not sure we can abuse dispatch like this to "infer" the schema. Seems to work...
  def left(v: Int): Either =
    srow(eitherStructType(IntegerType, DataTypes.NullType), v, null)

  def left(v: Row): Either =
    srow(eitherStructType(v.schema, DataTypes.NullType), v, null)

  def right(v: Row): Either =
    srow(eitherStructType(DataTypes.NullType, v.schema), null, v)

  def none(): Either =
    srow(eitherStructType(DataTypes.NullType, DataTypes.NullType), null, null)

  // In general, there is no way to infer the types S and R.
  // We need to put annotations on the parameters of left and right during codegen.
  def either[L, T, R](v: Either, left: (L) => T, right: (R) => T): T =
    if (v.isNullAt(0)) right(v.getAs[R]("$right"))
    else left(v.getAs[L]("$left"))

  /* Brands
 * ======
 *
 * We represent a branded value as a row with two fields: data and type.
 * TODO What happens if we brand a branded value?
 */

  type Brand = String
  type BrandedValue = Row

  def brandStructType(t: DataType): StructType =
    StructType(StructField("$data", t, false)
      :: StructField("$type", ArrayType(StringType, false), false) :: Nil)

  // Same thing as with either, need to infer/pass the Spark type. Can we factor this out?
  def brand(v: Int, b: Brand*): BrandedValue =
    srow(brandStructType(IntegerType), v, b)

  def brand(v: Row, b: Brand*): BrandedValue =
    srow(brandStructType(v.schema), v, b)

  def unbrand[T](bv: BrandedValue): T =
    bv.getAs[T]("$data")

  // TODO
  def isSubBrand(a: Brand, b: Brand) =
    false

  def reshape(v: Any, t: DataType): Any = (v, t) match {
    case (i: Int, t: IntegerType) => i
    case (s: String, t: StringType) => s
    case (b: Boolean, t: BooleanType) => b
    case (r: Row, t: StructType) => t.fieldNames match {
      case Array("$blob", "$known") =>
        val blob = r.getAs[String]("$blob")
        // NOTE We get all the known fields from the blob. If we ever decide to only keep unknown fields in the blob we have to change this.
        val known = fromBlob(t("$known").dataType, blob)
        srow(t, blob, known)
      // TODO incomplete
      }
    // TODO incomplete
  }

  /** QCert cast operator
    *
    * @param v The value has to be a branded value, that is a Row with fields $data : τ and $type : Array[String].
    * @param t The intersection type of the brands we are casting to. The data will be reshaped to match this type.
    * @param bs The brands we are casting to.
    * @return Either a right, if the cast fails, or a branded value with the data reshaped to fit the intersection.
    */
  def cast(v: BrandedValue, t: DataType, bs: Brand*): Either = {
    // First, check whether the cast succeds, that is, for every brand to cast to, is there a runtime tag that is a subtype
    if (!bs.forall((brand: Brand) => {
      v.getAs[Seq[Brand]]("$type").exists((typ: Brand) => {
        typ == brand || isSubBrand(typ, brand)
      })
    })) return none()
    // Second, if the cast succeeds, reshape data to match the intersection type
    val data = v.get(v.fieldIndex("$data"))
    val reshaped = reshape(data, t).asInstanceOf[Row] // TODO this cast is wrong. Write a brand(Any, Brand*) method
    left(brand(reshaped, v.getSeq[String](v.fieldIndex("$type")):_*))
  }

  /* Bags
   * ====
   *
   */
  // type Bag[T] = Array[T] // Huh, with Bag alias overloading does not work.

  def arithMean(b: Array[Int]): Double =
    if (b.length == 0) 0.0
    // Cast, because it's 1960 and we don't know how to do arithmetic properly, so our default / is integer division.
    else b.sum.asInstanceOf[Double] / b.length

  def arithMean(b: Array[Double]): Double =
    if (b.length == 0) 0.0
    else b.sum / b.length

  /*
  def distinct[T](b: Array[T])(implicit m: ClassTag[T]): Array[T] = {
    val set = new util.TreeSet(new QCertComparator[T]())
    val a = util.Arrays.asList(b: _*)
    for (x <- b)
      set.add(x)
    val res = new Array[T](set.size())
    var i = 0
    for (x <- scala.collection.JavaConversions.asScalaIterator(set.iterator())) {
      res(i) = x
      i += 1
    }
    res
  }*/

  /* Sorting & equality
 * ==================
 */
  object QCertOrdering extends Ordering[Any] {
    def compare(x: Any, y: Any): Int = (x, y) match {
      // NULL sorts before anything else
      case (null, null) => 0
      case (null, _) => -1
      case (_, null) => 1
      // Boolean, false sorts before true
      case (false, false) => 0
      case (false, true) => -1
      case (true, false) => 1
      case (true, true) => 0
      // Other primitive types
      case (x: Int, y: Int) => x compareTo y
      case (x: Double, y: Double) => x compareTo y
      case (x: String, y: String) => x compareTo y
      // Bags
      case (a: Array[_], b: Array[_]) =>
        // Shorter arrays sort before longer arrays
        if (a.length.compareTo(b.length) != 0)
          return a.length.compareTo(b.length)
        // Sort elements
        val lt = compare(_: Any, _: Any) < 0
        val l = List(a: _*).sortWith(lt)
        val r = List(b: _*).sortWith(lt)
        // The first unequal element between the two arrays determines array sort order
        for ((le, re) <- l zip r) {
          if (le < re)
            return -1
          if (le > re)
            return 1
        }
        0
      // Records
      case (a: Row, b: Row) =>
        // This assumes fields are in lexicographic order (by field name)!
        for ((le, re) <- a.toSeq zip b.toSeq) {
          if (le < re)
            return -1
          if (le > re)
            return 1
        }
        0
    }
  }

  class QCertComparator[T] extends Comparator[T] {
    def compare(a: T, b: T): Int = QCertOrdering.compare(a, b)
  }

  def equal(a: Any, b: Any) =
    QCertOrdering.compare(a, b) == 0
}
