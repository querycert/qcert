{"inheritance": []
,"model":
{"modelName": "test01",
 "brandTypes" :[],
   "typeDefs" :[]
}
, "WMType" : { "$coll" : { "cid": "Nat", "age": "Nat", "name": "String"} },
"input": [
  {"name":"John Doe", "cid":123, "age":32},
  {"name":"Jane Doe", "cid":124, "age":32},
  {"name":"Jim Does", "cid":125, "age":34},
  {"name":"Jill Does", "cid":126, "age":32},
  {"name":"Joan Doe", "cid":127, "age":34},
  {"name":"James Do", "cid":128, "age":35}
  ],

"partitionedInput": {
  "entities.Customer":[
    {"name":"Jane Doe", "cid":124, "age":32},
    {"name":"Joan Doe", "cid":127, "age":34},
    {"name":"Jill Does", "cid":126, "age":32},
    {"name":"John Doe", "cid":123, "age":32},
    {"name":"Jim Does", "cid":125, "age":34},
    {"name":"James Do", "cid":128, "age":35}]
},

"output": [
  "Customer =John Doe",
  "Customer =Jane Doe",
  "Customer =Jill Does"
]}
