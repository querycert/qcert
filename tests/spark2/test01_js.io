{"inheritance": [
{"sub":"entities.MainEntity", "sup":"org.qcert.TopEntity"},
   {"sub":"entities.Purchase", "sup":"org.qcert.TopEntity"},
   {"sub":"entities.Customer", "sup":"org.qcert.TopEntity"}
]
,"model":
{"modelName": "test01",
 "brandTypes" :[{ "brand":"org.qcert.TopEntity", "typeName":"org_qcert_TopEntity"},
   { "brand":"entities.Customer", "typeName":"entities_Customer"},
   { "brand":"entities.Purchase", "typeName":"entities_Purchase"},
   { "brand":"entities.MainEntity", "typeName":"entities_MainEntity"}],
   "typeDefs" :[{ "typeName": "org_qcert_TopEntity", "typeDef": { }},
   { "typeName": "entities_Customer", "typeDef": { "cid": "Nat", "age": "Nat", "name": "String"}},
   { "typeName": "entities_Purchase", "typeDef": { "cid": "Nat", "pid": "Nat", "name": "String", "quantity": "Nat"}},
   { "typeName": "entities_MainEntity", "typeDef": { "id": "Nat", "doubleAttribute": "Nat", "stringId": "String"}}]
}
, "WMType" : { "$coll" : { "$brand" : ["entities.MainEntity"] } },
"input": [
  {"type":["entities.Customer"],"data":{"name":"John Doe", "cid":123, "age":32}},
  {"type":["entities.Customer"],"data":{"name":"Jane Doe", "cid":124, "age":32}},
  {"type":["entities.Customer"],"data":{"name":"Jim Does", "cid":125, "age":34}},
  {"type":["entities.Customer"],"data":{"name":"Jill Does", "cid":126, "age":32}},
  {"type":["entities.Customer"],"data":{"name":"Joan Doe", "cid":127, "age":34}},
  {"type":["entities.Customer"],"data":{"name":"James Do", "cid":128, "age":35}},
  {"type":["entities.Purchase"],"data":{"name":"Tomatoe", "cid":123, "pid":1, "quantity":3}},
  {"type":["entities.Purchase"],"data":{"name":"Potatoe", "cid":123, "pid":2, "quantity":1}},
  {"type":["entities.Purchase"],"data":{"name":"Stiletto", "cid":125, "pid":3, "quantity":64}},
  {"type":["entities.Purchase"],"data":{"name":"Libretto", "cid":126, "pid":4, "quantity":62}},
  {"type":["entities.Purchase"],"data":{"name":"Dough", "cid":128, "pid":5, "quantity":4}},
  {"type":["entities.Purchase"],"data":{"name":"Croissant", "cid":128, "pid":6, "quantity":2}},
  {"type":["entities.MainEntity"],"data":{"id":201, "doubleAttribute":4, "stringId":"201"}},
  {"type":["entities.MainEntity"],"data":{"id":202, "doubleAttribute":100, "stringId":"202"}}
],

"partitionedInput": {"entities.Purchase":[
    {"type":["entities.Purchase"],"data":{"name":"Stiletto", "cid":125, "pid":3, "quantity":64}},
    {"type":["entities.Purchase"],"data":{"name":"Dough", "cid":128, "pid":5, "quantity":4}},
    {"type":["entities.Purchase"],"data":{"name":"Tomatoe", "cid":123, "pid":1, "quantity":3}},
    {"type":["entities.Purchase"],"data":{"name":"Libretto", "cid":126, "pid":4, "quantity":62}},
    {"type":["entities.Purchase"],"data":{"name":"Croissant", "cid":128, "pid":6, "quantity":2}},
    {"type":["entities.Purchase"],"data":{"name":"Potatoe", "cid":123, "pid":2, "quantity":1}}],
  "entities.MainEntity":[
    {"type":["entities.MainEntity"],"data":{"id":201, "doubleAttribute":4, "stringId":"201"}},
    {"type":["entities.MainEntity"],"data":{"id":202, "doubleAttribute":100, "stringId":"202"}}],
  "entities.Customer":[
    {"type":["entities.Customer"],"data":{"name":"Jane Doe", "cid":124, "age":32}},
    {"type":["entities.Customer"],"data":{"name":"Joan Doe", "cid":127, "age":34}},
    {"type":["entities.Customer"],"data":{"name":"Jill Does", "cid":126, "age":32}},
    {"type":["entities.Customer"],"data":{"name":"John Doe", "cid":123, "age":32}},
    {"type":["entities.Customer"],"data":{"name":"Jim Does", "cid":125, "age":34}},
    {"type":["entities.Customer"],"data":{"name":"James Do", "cid":128, "age":35}}]
},

"output": [
  "Customer =John Doe",
  "Customer =Jane Doe",
  "Customer =Jill Does"
]}
