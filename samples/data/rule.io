{"schema": { 
    "inheritance": [
	{"sub":"entities.MainEntity", "sup":"com.ibm.ia.model.Entity"},
	{"sub":"entities.Purchase", "sup":"com.ibm.ia.model.Entity"},
	{"sub":"entities.Customer", "sup":"com.ibm.ia.model.Entity"}
    ],
    "brandTypes" :[{ "brand":"com.ibm.ia.model.Entity", "typeName":"com_ibm_ia_model_Entity"},
		   { "brand":"entities.Customer", "typeName":"entities_Customer"},
		   { "brand":"entities.Purchase", "typeName":"entities_Purchase"},
		   { "brand":"entities.MainEntity", "typeName":"entities_MainEntity"}],
    "typeDefs" :[{ "typeName": "com_ibm_ia_model_Entity", "typeDef": { }},
		 { "typeName": "entities_Customer", "typeDef": { "cid": "Nat", "age": "Nat", "name": "String"}},
		 { "typeName": "entities_Purchase", "typeDef": { "cid": "Nat", "pid": "Nat", "name": "String", "quantity": "Nat"}},
		 { "typeName": "entities_MainEntity", "typeDef": { "id": "Nat", "doubleAttribute": "Nat", "stringId": "String"}}],
    "globals" : { "WORLD" : { "dist" : "distr", "type" : { "$coll" : { "$brand" : ["entities.MainEntity"] } } } }
}
,
"input": { "WORLD" : [
  {"type":["entities.Customer"],"data":{"name":"John Doe", "cid":123, "age":32}},
  {"type":["entities.Customer"],"data":{"name":"Jane Doe", "cid":124, "age":32}},
  {"type":["entities.Customer"],"data":{"name":"Jim Does", "cid":125, "age":34}},
  {"type":["entities.Customer"],"data":{"name":"Jill Does", "cid":126, "age":32}},
  {"type":["entities.Customer"],"data":{"name":"Joan Doe", "cid":127, "age":34}},
  {"type":["entities.Customer"],"data":{"name":"James Do", "cid":128, "age":35}},
  {"type":["entities.Purchase"],"data":{"name":"Tomatoe", "cid":123, "quantity":3, "pid":1}},
  {"type":["entities.Purchase"],"data":{"name":"Potatoe", "cid":123, "quantity":1, "pid":2}},
  {"type":["entities.Purchase"],"data":{"name":"Stiletto", "cid":125, "quantity":64, "pid":3}},
  {"type":["entities.Purchase"],"data":{"name":"Libretto", "cid":126, "quantity":62, "pid":4}},
  {"type":["entities.Purchase"],"data":{"name":"Dough", "cid":128, "quantity":4, "pid":5}},
  {"type":["entities.Purchase"],"data":{"name":"Croissant", "cid":128, "quantity":2, "pid":6}},
  {"type":["entities.MainEntity"],"data":{"id":201, "doubleAttribute":4, "stringId":"201"}},
  {"type":["entities.MainEntity"],"data":{"id":202, "doubleAttribute":100, "stringId":"202"}}
] },
"output": [
  "Customer =John Doe",
  "Customer =Jane Doe",
  "Customer =Jill Does"
]}

