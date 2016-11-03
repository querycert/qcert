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
  "Persons" :
  [{"pid": 1, "name": "John Doe", "age":32, "company":101},
   {"pid": 2, "name": "Jane Doe", "age":32, "company":103},
   {"pid": 3, "name": "Jim Does", "age":34, "company":101},
   {"pid": 4, "name": "Jill Does","age":32, "company":102},
   {"pid": 5, "name": "Joan Doe", "age":34, "company":101},
   {"pid": 6, "name": "James Do", "age":35, "company":103}],
  "Companies" :
  [ {"cid": 101, "cname": "Blue Widget", "departments" : [ "Sales", "Manufacturing" ] },
    {"cid": 102, "cname": "Pimble", "departments" : [] },
    {"cid": 103, "cname": "Unter", "departments" : ["IP","M&A","Sales"] } ]
},

"output": [
  "Customer =John Doe",
  "Customer =Jane Doe",
  "Customer =Jill Does"
]}
