Spark2 runtime design notes
===========================

We need a data representation that supports the rich data model of QCert, while being close enough to what SparkSQL natively supports to take advantage of its efficient execution without converting data back and forth.

Spark data model
----------------

When we talk about the Spark data model, we mean the subset that you can easily work with using SparkSQL.
Spark's core data model is the Resilient Distributed Dataset (RDD).
You can stick pretty much anything into an RDD.
Similarly, Datasets hold arbitrary case classes.
However, for easy interoperability between plain Spark and SparkSQL, we want to only use the Dataframe data model.

SparkSQL operates on a mostly relational data model, that is tables, or Dataframes.
Fortunately, Dataframes are not *just* flat relations.
Data starts with a distributed collection of basically tabular data.
This is called a Dataframe, which might eventually become an alias for `Dataset[Row]`.


QCert data in Spark
-------------------

QCert supports a richer datamodel than Spark.
The types of data in QCert with nonobvious counterparts in Spark are open records, either, and brands.
Brands introduce subtyping, with top and bottom types.

Subtyping and open records expose a common difficulty:
The shape of data is no longer obvious from its type.
For example, since everything is a subtype of Top, we can have a heterogenous (in the type) collection of arbitrary things, at type collection of Top.
In Spark, Datasets and nested arrays have to be homogenous, so to make this work we need a common representation for all data.
We chose a JSON serialization.
Note that we only need this for data inside the unknown part of open records and things at type Top.
Since there is nothing you can *do* with this data except for passing it along, casting, comparing for equality, and printing it, the performance hit is expected to be small.


TODO
----

details for

- Any
- Brands (recursion!)
- Casts are potentially expensive (can we quantify that?)
- D ;)
- Either
- Open records
- Bags (sorted?, for equality (sorting is not enough to use built-in equality if we have to deserialize for equality..))
- Equality (esp. open and closed records)
