{ 
  "WMType": { 
    "$coll": { 
      "$brand": [ 
        "entities.Ranking" 
      ] 
    } 
  }, "inheritance": [ 
    { 
      "sub": "entities.Ranking", "sup": "org.qcert.TopEntity" 
    } 
  ], "input": [], "model": { 
    "brandTypes": [ 
      { 
        "brand": "org.qcert.TopEntity", "typeName": 
        "org_qcert_TopEntity" 
      }, { 
        "brand": "entities.Ranking", "typeName": 
        "entities_Ranking" 
      } 
    ], "modelName": "test01", "typeDefs": [ 
      { 
        "typeDef": { }, "typeName": "org_qcert_TopEntity" 
      }, { 
        "typeDef": { 
          "avgDuration": "Nat", "pageRank": "Nat", "pageURL": 
          "String" 
        }, "typeName": "entities_Ranking" 
      } 
    ] 
  }, "output": [], "partitionedInput": null 
}
