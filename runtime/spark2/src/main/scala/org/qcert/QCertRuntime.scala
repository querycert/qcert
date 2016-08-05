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

import com.google.gson.JsonElement
import org.apache.spark.sql.catalyst.expressions.GenericRowWithSchema
import org.apache.spark.sql.types._
import org.apache.spark.sql.{DataFrame, Dataset, Row, SparkSession}
import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.sql.functions._

import scala.collection.mutable
import scala.collection.JavaConverters._

object test extends QCertRuntime {
  val worldType = StructType(Seq(StructField("$data", StringType), StructField("$type", ArrayType(StringType))))

  override def run(CONST$WORLD: Dataset[Row]): Unit = {
    val res = {CONST$WORLD.select(lit(null).equalTo(lit(null)))}


    res.explain(true)

    res.show()

    res.collect().map((row) => row(0)).foreach(println(_))

  }
}

/** QCertRuntime static functions
  *
  * Turns out SparkSQL only accepts locally bound lambdas and static functions as user-defined functions.
  * Most of the runtime functions are declared in the abstract class QCertRuntime, which makes them methods.
  *
  * TODO move more of the runtime in here, so it can potentially be used from SparkSQL
  *
  * We cannot get rid of the QCertRuntime *class* completely:
  * The class has the main method (which cannot be in the object, even though it is static?!?)
  * It declares abstract members like `run` and the world type for initial data loading.
  */
object QCertRuntime {
  def toQCertString(x: Any): String = x match {
    case null => "UNIT" // null is unit, right?
    case x: Int => x.toString
    case true => "TRUE"
    case false => "FALSE"
    case x: String => x // no quotes!
    case x: Array[_] => x.map(QCertRuntime.toQCertString).mkString("[", ", ", "]")
    // Open records, as always, are being bloody difficult...
    case x: Row => x.toString // TODO
  }

  def toQCertStringUDF =
    udf((x: Any) => QCertRuntime.toQCertString(x), StringType)

  // TODO
  // We might want to change all of these to pass around a runtime support object with the hierarchy, gson parser, ...
  // basically everything that's currently in the QCertRuntime abstract class

  def isSubBrand(brandHierarchy: mutable.HashMap[String, mutable.HashSet[String]], sub: String, sup: String): Boolean = {
    if (sub == sup || sup == "Any")
      return true
    brandHierarchy.getOrElse(sub, Seq()).exists(dsup => isSubBrand(brandHierarchy, dsup, sup))
  }

  def castUDFHelper(h: mutable.HashMap[String, mutable.HashSet[String]], bs: String*) = (ts: mutable.WrappedArray[String]) =>
    bs.forall((brand: String) =>
      ts.exists((typ: String) =>
        isSubBrand(h, typ, brand)))

  // TODO Can we somehow avoid passing the hierarchy at every call site?
  def castUDF(h: mutable.HashMap[String, mutable.HashSet[String]], bs: String*) =
    udf(QCertRuntime.castUDFHelper(h, bs:_*), BooleanType)

  def srow(s: StructType, vals: Any*): Row = {
    assert(s.fields.length == vals.length,
      "Number of record fields does not match the schema. Did you forget to splice an array parameter?")
    assert(s.fieldNames.sorted.distinct.sameElements(s.fieldNames),
      "Field names must be unique and sorted!")
    new GenericRowWithSchema(vals.toArray, s)
  }

  def fromBlob(t: DataType, b: JsonElement): Any = t match {
    case t: IntegerType => b.getAsInt
    case t: BooleanType => b.getAsBoolean
    case t: StringType => b.getAsString
    case t: ArrayType =>
      b.getAsJsonArray.iterator().asScala.map((e: JsonElement) => fromBlob(t.elementType, e)).toArray
    case t: StructType => t.fieldNames match {
      case Array("$left", "$right") => sys.error("either")
      case Array("$type", "$data") => sys.error("brand")
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

  def fromBlob(t: DataType, b: String): Any =
    // TODO because this is static now, we instantiate a new gson parser every time, fix this
    fromBlob(t, new com.google.gson.JsonParser().parse(b))

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
}

abstract class QCertRuntime {
  // TODO revisit naming -- we don't want to clash with spark.sql.functions._ functions

  val gson = new com.google.gson.Gson()
  val gsonParser = new com.google.gson.JsonParser()

  def run(world: Dataset[Row])

  def addToBrandHierarchy(sub: String, sup: String): Unit = {
    brandHierarchy.get(sub) match {
      case None => brandHierarchy += sub -> mutable.HashSet(sup)
      case Some(hs) => hs += sup
    }
  }

  val worldType: StructType
  val sparkContext = new SparkContext("local", "QCERT", new SparkConf())
  val sparkSession = SparkSession.builder().getOrCreate()


  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      println("Expected exactly one argument: the sparkio file containing the data")
      sys.exit(1)
    }
    val iofileData = args(0)

    println("Brand hierarchy:")
    println(brandHierarchy)

    // val jsonFile = "/Users/stefanfehrenbach/global-rules/docs/notes/test07-sparkio.json"
    val df0 = sparkSession.read.schema(worldType).json(iofileData)
    //printing some debugging output for sanity-checking
    System.out.println("--- input schema ---")
    df0.printSchema()
    System.out.println("--- input documents ---")
    df0.show()

    println("about to call run(df0)")
    print("[RESULT] ")
    run(df0)
    println("about to call sparkContext.stop()")
    sparkContext.stop()
  }

  // TODO handle bags of non-Row types (Int, String, Bags, ...)
  def dispatch(schema: StructType, a: Array[Row]): DataFrame = {
    val l: util.List[Row] = a.toList.asJava
    sparkSession.createDataFrame(l, schema)
  }

  def fromBlob(t: DataType, b: JsonElement): Any = t match {
    case t: IntegerType => b.getAsInt
    case t: BooleanType => b.getAsBoolean
    case t: StringType => b.getAsString
    case t: ArrayType =>
      b.getAsJsonArray.iterator().asScala.map((e: JsonElement) => fromBlob(t.elementType, e)).toArray
    case t: StructType => t.fieldNames match {
      case Array("$left", "$right") => sys.error("either")
      case Array("$type", "$data") => sys.error("brand")
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

  def fromBlob(t: DataType, b: String): Any =
    fromBlob(t, gsonParser.parse(b))

  def toBlob(v: Any): String = v match {
    case i: Int => i.toString
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
      case _ => sys.error("Illformed record schema: " ++ r.schema.toString())
    }
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
    // What we should do is use QCert equality. Unfortunately, we would need to deserialize for that, which we can't, because we don't have the type!
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

  def unbrand[T](t: DataType, v: BrandedValue): T = {
    // Second, if the cast succeeds, reshape data to match the intersection type
    val data = v.get(v.fieldIndex("$data"))
    // TODO this cast is wrong, we need a reshape/fromBlob that actually produces the correct type!
    val reshaped = reshape(data, t).asInstanceOf[T]
    reshaped
  }

  // From sub type to immediate super types
  val brandHierarchy = mutable.HashMap[String, mutable.HashSet[String]]()

  // TODO replace by static helper
  def isSubBrand(brandHierarchy: mutable.HashMap[String, mutable.HashSet[String]], sub: Brand, sup: Brand): Boolean = {
    if (sub == sup || sup == "Any")
      return true
    brandHierarchy.getOrElse(sub, Seq()).exists(dsup => isSubBrand(brandHierarchy, dsup, sup))
  }

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
    case (blob: String, t: StructType) => t.fieldNames match {
      case Array("$blob", "$known") => fromBlob(t, blob)
      // TODO incomplete
    }
    // TODO incomplete
  }

  /** QCert cast operator (DNRC version)
    *
    * This is not a general cast operator, i.e. it does not give access to fields from the .. part of
    * an open record. The input has to be a branded value.
    *
    * @param v  The value has to be a branded value, that is a Row with fields $data : τ and $type : Array[String].
    * @param bs The brands we are casting to.
    * @return Either a right, if the cast fails, or a branded value wrapped in left.
    */
  def cast(v: BrandedValue, bs: Brand*): Either = {
    // TODO use castUDF helper
    if (!bs.forall((brand: Brand) =>
      v.getAs[Seq[Brand]]("$type").exists((typ: Brand) =>
        isSubBrand(brandHierarchy, typ, brand))))
      none()
    else
      left(v)
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

  // We can do O(1) min and max, because we keep bags sorted
  // The default 0 for empty bags comes from the Coq semantics
  def anummax(b: Array[Int]): Int =
    if (b.isEmpty) 0 else b(b.length-1)

  def anummin(b: Array[Int]): Int =
    if (b.isEmpty) 0 else b(0)

  /** Binary operator AContains */
  def AContains[T](e: T, l: Array[T]): Boolean =
    l.exists(QCertOrdering.compare(e, _) == 0)

  /* Sorting & equality
 * ==================
 */
  object QCertOrdering extends Ordering[Any] {
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
    }
  }

  class QCertComparator[T] extends Comparator[T] {
    def compare(a: T, b: T): Int = QCertOrdering.compare(a, b)
  }

  def equal(a: Any, b: Any): Boolean =
    QCertOrdering.compare(a, b) == 0


  def lessOrEqual(a: Any, b: Any): Boolean =
    QCertOrdering.compare(a, b) <= 0

  def lessThan(a: Any, b: Any): Boolean =
    QCertOrdering.compare(a, b) < 0
}
