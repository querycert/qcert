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
  [ {"pid": 1, "name": "John Doe", "age":32, "company":101},
    {"pid": 2, "name": "Jane Doe", "age":32, "company":103},
    {"pid": 3, "name": "Jim Does", "age":34, "company":101},
    {"pid": 4, "name": "Jill Does","age":32, "company":102},
    {"pid": 5, "name": "Joan Doe", "age":34, "company":101},
    {"pid": 6, "name": "James Do", "age":35, "company":103} ],
  "Companies" :
  [ {"cid": 11, "cname": "Blue Widget" },
    {"cid": 12, "cname": "Pimble" },
    {"cid": 13, "cname": "Unter" } ],
  "Departments" :
  [ {"did": 101, "dcompany": 101, "dname" : "Sales" },
    {"did": 102, "dcompany": 101, "dname" : "Manufacturing" },
    {"did": 103, "dcompany": 103, "dname" : "IP" },
    {"did": 104, "dcompany": 103, "dname" : "M&A" },
    {"did": 105, "dcompany": 103, "dname" : "Sales" } ]
},

"output": [
  "Customer =John Doe",
  "Customer =Jane Doe",
  "Customer =Jill Does"
]}
