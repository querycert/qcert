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

import java.util
import java.util.Comparator

import com.google.gson.{GsonBuilder, JsonElement}
import org.apache.spark.sql.catalyst.expressions.GenericRowWithSchema
import org.apache.spark.sql.types._
import org.apache.spark.sql.{DataFrame, Dataset, Row, SparkSession}
import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.sql.functions._

import scala.collection.mutable
import scala.collection.JavaConverters._


/** QcertRuntime static functions
  *
  * Turns out SparkSQL only accepts locally bound lambdas and static functions as user-defined functions.
  * Most of the runtime functions are declared in the abstract class QcertRuntime, which makes them methods.
  *
  * TODO move more of the runtime in here, so it can potentially be used from SparkSQL
  *
  * We cannot get rid of the QcertRuntime *class* completely:
  * The class has the main method (which cannot be in the object, even though it is static?!?)
  * It declares abstract members like `run` and the world type for initial data loading.
  */
object QcertRuntime {

  var timer: Long = 0

  def beforeQuery() = {
    timer = System.currentTimeMillis()
  }

  def afterQuery() = {
    val took = System.currentTimeMillis() - timer
    // Not sure this works on Spark / Amazon EMR
    // In general, sometimes output does not show up, using System.out or Console.out ...
    Console.out.print(Console.GREEN)
    Console.out.println(s"After query, evaluation took ${took} ms")
    Console.out.println(Console.RESET)
  }

  type BrandInheritance = Map[String, Set[String]]
  def makeInheritance(args: (String, String)*) : BrandInheritance = {
    val brandInheritance = mutable.HashMap[String, mutable.HashSet[String]]()
    def addToBrandInheritance(p : (String, String)) = p match {
      case (sub, sup) =>
        brandInheritance.get(sub) match {
          case None => brandInheritance += sub -> mutable.HashSet(sup)
          case Some(hs) => hs += sup
        }
    }
    args.foreach(addToBrandInheritance)
    brandInheritance.mapValues(_.toSet).toMap
  }

  def blobToQcertString(x: String): String = x // TODO

  def toQcertString(x: Any): String = x match {
    case null => "UNIT" // null is unit, right?
    case x: Int => x.toString
    case x: Long => x.toString
    case x: Float => x.toString
    case x: Double => x.toString
    case true => "TRUE"
    case false => "FALSE"
    case x: String => x // no quotes!
    case x: Array[_] => x.map(QcertRuntime.toQcertString).mkString("[", ", ", "]")
    case x: Row => x.schema.fieldNames match {
      case Array("$left", "$right") =>
        if (x.isNullAt(0))
          "Right(" + toQcertString(x(0)) + ")"
        else
          "Left(" + toQcertString(x(1)) + ")"
      case Array("$type", "$data") =>
        val brands = x.getSeq[String](0).mkString(" & ")
        val data = blobToQcertString(x.getAs[String](1))
        s"<$brands:$data>"
      case Array("$blob", "$known") =>
        blobToQcertString(x.getAs[String](0))
    }
  }

  def toQcertStringUDF =
    udf((x: Any) => QcertRuntime.toQcertString(x), StringType)

  // TODO
  // We might want to change all of these to pass around a runtime support object with the inheritance, gson parser, ...
  // basically everything that's currently in the QcertRuntime abstract class

  def isSubBrand(brandInheritance: BrandInheritance, sub: String, sup: String): Boolean = {
    if (sub == sup || sup == "Any")
      return true
    brandInheritance.getOrElse(sub, Seq()).exists(dsup => isSubBrand(brandInheritance, dsup, sup))
  }

  def castUDFHelper(h: BrandInheritance, bs: String*) = (ts: mutable.WrappedArray[String]) =>
    bs.forall((brand: String) =>
      ts.exists((typ: String) =>
        isSubBrand(h, typ, brand)))

  // TODO Can we somehow avoid passing the inheritance at every call site?
  def castUDF(h: BrandInheritance, bs: String*) =
    udf(QcertRuntime.castUDFHelper(h, bs:_*), BooleanType)

  def reshape(v: Any, t: DataType): Any = (v, t) match {
    case (i: Int, t: LongType) => i.toLong
    case (i: Long, t: LongType) => i
    case (f: Float, t: FloatType) => f
    case (d: Double, t: DoubleType) => d
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
    case (blob: String, t: StructType) => t.fieldNames match {
      case Array("$blob", "$known") => fromBlob(t, blob)
      // TODO incomplete
    }
    // TODO incomplete
  }

  def unbrandUDF[T](t: DataType) = {
    /* Work around a bug in the SparkSQL optimizer
     *
     * https://issues.apache.org/jira/browse/SPARK-13773
     *
     * reshape is not total, it expects the data and type to match up.
     * If the data does not match the type, it will throw an exception.
     * Normally this does not happen, because the type checker ensures
     * that the data has the correct type. Most queries perform a cast
     * and then unbrand, if the cast succeeds. Due to a bug in the SparkSQL
     * optimizer, in some cases the order of operations gets turned around,
     * and we end up unbranding values that should not have passed the cast.
     *
     * We work around by making reshape "total" by returning null in case it
     * throws. This is not ideal, because the nulls may be used in further
     * filter conditions, but we assume SparkSQL built-ins deal with null
     * correctly. The nulls should not escape out of a filter condition,
     * because the cast condition is still checked, eventually.
     */
    def workaround(data: T, t: DataType) =
      try {
        reshape(data, t)
      } catch {
        case e: NullPointerException =>
          null
      }
    udf((data: T) => workaround(data, t), t)
  }

  type Brand = String
  type BrandedValue = Row

  def brandStructType(t: DataType): StructType =
    StructType(StructField("$data", t, false)
      :: StructField("$type", ArrayType(StringType, false), false) :: Nil)

  // Same thing as with either, need to infer/pass the Spark type. Can we factor this out?
  def brand(v: Long, b: Brand*): BrandedValue =
  srow(brandStructType(LongType), v, b)

  def brand(v: Row, b: Brand*): BrandedValue =
    srow(brandStructType(v.schema), v, b)

  def unbrand[T](t: DataType, v: BrandedValue): T = {
    // Second, if the cast succeeds, reshape data to match the intersection type
    val data = v.get(v.fieldIndex("$data"))
    // TODO this cast is wrong, we need a reshape/fromBlob that actually produces the correct type!
    val reshaped = reshape(data, t).asInstanceOf[T]
    reshaped
  }

  /** Qcert cast operator (DNRC version)
    *
    * This is not a general cast operator, i.e. it does not give access to fields from the .. part of
    * an open record. The input has to be a branded value.
    *
    * @param v  The value has to be a branded value, that is a Row with fields $data : τ and $type : Array[String].
    * @param bs The brands we are casting to.
    * @return Either a right, if the cast fails, or a branded value wrapped in left.
    */
  def cast(brandInheritance: BrandInheritance, v: BrandedValue, bs: Brand*): Either = {
    // TODO use castUDF helper
    if (!bs.forall((brand: Brand) =>
      v.getSeq(1 /* $type */).exists((typ: Brand) =>
        isSubBrand(brandInheritance, typ, brand))))
      none()
    else
      left(v)
  }

  type Either = Row

  def eitherStructType(l: DataType, r: DataType): StructType =
    StructType(StructField("$left", l, true) :: StructField("$right", r, true) :: Nil)

  // Not sure we can abuse dispatch like this to "infer" the schema. Seems to work...
  def left(v: Long): Either =
  srow(eitherStructType(LongType, DataTypes.NullType), v, null)

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

  val gson = new GsonBuilder().disableHtmlEscaping().create()
  val gsonParser = new com.google.gson.JsonParser()

  // TODO handle bags of non-Row types (Int, String, Bags, ...)
  def dispatch(sparkSession: SparkSession, schema: StructType, a: Array[Row]): DataFrame = {
    val l: util.List[Row] = a.toList.asJava
    sparkSession.createDataFrame(l, schema)
  }

  def fromBlob(t: DataType, b: JsonElement): Any = t match {
    case t: LongType => b.getAsLong
    case t: IntegerType => b.getAsLong
    case t: FloatType => b.getAsFloat
    case t: DoubleType => b.getAsDouble
    case t: BooleanType => b.getAsBoolean
    case t: StringType => b.getAsString
    case t: ArrayType =>
      b.getAsJsonArray.iterator().asScala.map((e: JsonElement) => fromBlob(t.elementType, e)).toArray
    case t: StructType => t.fieldNames match {
      case Array("$left", "$right") => sys.error("either")
      case Array("$data", "$type") =>
        srow(StructType(StructField("$data", StringType, false)
                     :: StructField("$type", ArrayType(StringType, false), false)
                     :: Nil),
             b.getAsJsonObject.get("data").toString,
             fromBlob(ArrayType(StringType, false), b.getAsJsonObject.get("type")))
      case Array("$blob", "$known") =>
        val r = b.getAsJsonObject
        val knownFieldValues = t("$known").dataType.asInstanceOf[StructType].fields map ((field: StructField) => {
          fromBlob(field.dataType, r.get(field.name))
        })
        srow(t,
          // We have the full record in the blob field, even for closed records
          r.toString,
          srow(t("$known").dataType.asInstanceOf[StructType], knownFieldValues: _*))
      case _ =>
        srow(t, t.fields.map((field) => fromBlob(field.dataType, b.getAsJsonObject.get(field.name))): _*)
    }
  }

  def fromBlob(t: DataType, b: String): Any = fromBlob(t, gsonParser.parse(b))

  def toBlob(v: Any): String = v match {
    case i: Int => i.toString
    case i: Long => i.toString
    case f: Float => f.toString
    case d: Double => d.toString
    case true => "true"
    case false => "false"
    case s: String => gson.toJson(s)
    case a: mutable.WrappedArray[_] =>
      a.map(toBlob(_)).mkString("[", ", ", "]")
    case a: Array[_] =>
      a.map(toBlob(_)).mkString("[", ", ", "]")
    case r: Row => r.schema.fieldNames match {
      case Array("$left", "$right") =>
        if (r.isNullAt(1))
          "{\"left\":" ++ toBlob(r(0))
        else
          "{\"right\":" ++ toBlob(r(1))
      case Array("$data", "$type") =>
        "{\"type\": " ++ toBlob(r(1)) ++ ", \"data\": " ++ toBlob(r(0)) ++ "}"
      case Array("$blob", "$known") =>
        // NOTE we keep the full record in the blob field
        r.getString(0)
      // TODO rename $value for consistency?
      case Array("value") =>
        toBlob(r(0))
      case _ => sys.error("Illformed record schema: " ++ r.schema.toString())
    }
    case () => "UNIT"
  }

  // TODO all record construction has to properly populate the blob field!
  type Record = Row

  /** More convenient record (row with schema) construction.
    * Splice array into varargs call: let a = Array(1, 2); srow(schema, a:_*) */
  def srow(s: StructType, vals: Any*): Row = {
    assert(s.fields.length == vals.length,
      "Number of record fields does not match the schema. Did you forget to splice an array parameter?")
    assert(s.fieldNames.sorted.distinct.sameElements(s.fieldNames),
      "Field names must be unique and sorted!")
    new GenericRowWithSchema(vals.toArray, s)
  }

  def recordConcat(l: Record, r: Record): Record = {
    def concatRows(l: Row, r: Row): Row = {
      val rightFieldNames = r.schema.fieldNames diff l.schema.fieldNames
      val allFieldNames = (rightFieldNames ++ l.schema.fieldNames).distinct.sorted
      val schema = allFieldNames.foldLeft(new StructType())((schema: StructType, field: String) => {
        val inLeft = l.schema.fieldNames.indexOf(field)
        schema.add(if (inLeft == -1) r.schema.fields(r.schema.fieldNames.indexOf(field)) else l.schema.fields(inLeft))
      })
      val names = l.schema.fieldNames ++ rightFieldNames
      val values = l.toSeq ++ rightFieldNames.map((rfn: String) => r.get(r.fieldIndex(rfn)))
      val sortedValues = (names zip values).sortBy(_._1).map(_._2)
      srow(schema, sortedValues: _*)
    }
    def concatBlobs(l: String, r: String): String = {
      val (left, right) = (gsonParser.parse(l).getAsJsonObject, gsonParser.parse(r).getAsJsonObject)
      val sortedResultMap = new java.util.TreeMap[String, JsonElement]()
      for (me <- right.entrySet().iterator().asScala)
        sortedResultMap.put(me.getKey, me.getValue)
      for (me <- left.entrySet().iterator().asScala)
        sortedResultMap.put(me.getKey, me.getValue)
      gson.toJson(sortedResultMap)
    }
    val known = concatRows(l.getAs("$known"), r.getAs("$known"))
    val blob = concatBlobs(l.getAs("$blob"), r.getAs("$blob"))
    srow(StructType(Seq(
      StructField("$blob", StringType),
      StructField("$known", known.schema))),
      blob,
      known)
  }

  def dot[T](n: String)(l: Record): T =
    l.getAs[Row]("$known").getAs[T](n)

  def mergeConcat(l: Record, r: Record): Array[Record] = {
    def allFieldNames(rr: Record) = {
      val known = rr.schema.fields(1).dataType.asInstanceOf[StructType].fieldNames
      val blob = gsonParser.parse(rr.getAs[String]("$blob")).getAsJsonObject.entrySet().iterator().asScala.map(e => e.getKey).toArray
      known.union(blob).distinct.sorted
    }
    def blobDot(n: String, r: Record) = gsonParser.parse(r.getAs[String]("$blob")).getAsJsonObject.get(n)
    val concatenated = recordConcat(l, r)
    val duplicates = allFieldNames(l) intersect allFieldNames(r)
    for (field <- duplicates)
    // TODO This uses JsonElement equality. Unless we can guarantee that the JSON serialization is unique, this is likely incorrect
    // What we should do is use Qcert equality. Unfortunately, we would need to deserialize for that, which we can't, because we don't have the type!
      if (blobDot(field, r) != blobDot(field, concatenated))
        return Array()
    Array(concatenated)
  }

  /** UnaryOp ARec */
  def singletonRecord(fieldName: String, fieldType: DataType, fieldValue: Any): Record = {
    val known = StructType(Seq(StructField(fieldName, fieldType)))
    val schema = StructType(Seq(
      StructField("$blob", StringType),
      StructField("$known", known)))
    srow(schema,
      "{\"" + fieldName + "\": " + toBlob(fieldValue) + "}",
      srow(known, fieldValue))
  }

  def recProject(fs: String*)(v: Record): Record = {
    val oldKnownSchema = v.schema.fields(1).dataType.asInstanceOf[StructType]
    val knownSchema = StructType(fs.map(f => oldKnownSchema.fields(oldKnownSchema.fieldIndex(f))))
    val data = v.get(1).asInstanceOf[GenericRowWithSchema]
    val knownValues = fs.map(data.getAs[Any])
    val known = srow(knownSchema, knownValues: _*)
    val jsonBlob = gsonParser.parse(v.getAs[String]("$blob")).getAsJsonObject
    val blobMap = new util.TreeMap[String, JsonElement]()
    for (f <- fs)
      blobMap.put(f, jsonBlob.get(f))
    val blob = gson.toJson(blobMap)
    srow(StructType(Seq(
      StructField("$blob", StringType),
      StructField("$known", knownSchema))),
      blob,
      known)
  }

  /* Bags
   * ====
   *
   */
  // type Bag[T] = Array[T] // Huh, with Bag alias overloading does not work.

  def arithMean(b: Array[Long]): Double =
    if (b.length == 0) 0.0
    // Cast, because it's 1960 and we don't know how to do arithmetic properly, so our default / is integer division.
    else b.sum.asInstanceOf[Double] / b.length

  def arithMean(b: Array[Double]): Double =
    if (b.length == 0) 0.0
    else b.sum / b.length

  /*
  def distinct[T](b: Array[T])(implicit m: ClassTag[T]): Array[T] = {
    val set = new util.TreeSet(new QcertComparator[T]())
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

  // We can do O(1) min and max, because we keep bags sorted
  // The default 0 for empty bags comes from the Coq semantics
  def anummax(b: Array[Long]): Long =
    if (b.isEmpty) 0 else b(b.length-1)

  def anummin(b: Array[Long]): Long =
    if (b.isEmpty) 0 else b(0)

  /** Binary operator AContains */
  def AContains[T](e: T, l: Array[T]): Boolean =
    l.exists(QcertOrdering.compare(e, _) == 0)

  /* Sorting & equality
 * ==================
 */
  object QcertOrdering extends Ordering[Any] {
    def compare(x: Any, y: Any): Int = (x, y) match {
      // TODO how to sort ()?
      case ((), ()) => 0
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
      case (x: Int, y: Long) => x.toLong compareTo y
      case (x: Long, y: Int) => x compareTo y
      case (x: Long, y: Long) => x compareTo y
      case (x: Float, y: Float) => x compareTo y
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
      // TODO this is copy&pasted from above -- factor out, support combinations, or find something more general
      case (a: mutable.WrappedArray[_], b: mutable.WrappedArray[_]) =>
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
      case (a, b) =>
        throw new Exception("Don't know how to compare a: " + a.getClass + " = " + a + " to b: " + b.getClass + " = " + b)
    }
  }

  class QcertComparator[T] extends Comparator[T] {
    def compare(a: T, b: T): Int = QcertOrdering.compare(a, b)
  }

  def equal(a: Any, b: Any): Boolean =
    QcertOrdering.compare(a, b) == 0


  def lessOrEqual(a: Any, b: Any): Boolean =
    QcertOrdering.compare(a, b) <= 0

  def lessThan(a: Any, b: Any): Boolean =
    QcertOrdering.compare(a, b) < 0
}
