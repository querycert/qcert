{ "schema": { "hierarchy": [],
	      "brandTypes" :[],
	      "typeDefs" :[],
	      "globals" :
	      { "Persons" :
		{ "dist" : "distr",
		  "type" : { "$coll" : { "pid" : "Nat" ,
					 "name" : "String",
					 "age" : "Nat",
					 "company" : "Nat" } } } }
	    },
  "input": { "Persons" :
	     [{"pid": 1, "name": "John Doe", "age":32, "company":101},
	      {"pid": 2, "name": "Jane Doe", "age":32, "company":103},
	      {"pid": 3, "name": "Jim Does", "age":34, "company":101},
	      {"pid": 4, "name": "Jill Does","age":32, "company":102},
	      {"pid": 5, "name": "Joan Doe", "age":34, "company":101},
	      {"pid": 6, "name": "James Do", "age":35, "company":103}] },
  "output": []
}
