import { Error, Request, Response, Credentials, DeployIn, DeployOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & DeployIn
export type ListOut = Credentials & DeployOut

const main = async (eparams:Request<ListIn>) : Promise<Response<ListOut>> => {
    // Propagate error
    if ((<Error>eparams).hasOwnProperty('error')) {
	const error: Error = (<Error>eparams);
	return error;
    }

    const params: ListIn = <ListIn>eparams;
    
    const pkgname: string = params.pkgname;
    const designs: Designs = params.querycode;

    // Create post-processing action
    const computeEffectiveParams = (effParams:string[]) : string => {
	let result = [ ];
	for (var i=0; i < effParams.length; i++) {
	    const param = effParams[i];
	    result.push("const "+ param +" = yield getView(\""+param+"\");");
	}
	return result.join('\n');
    }
    const makeEffectiveParams = (effParams:string[]) : string => {
	return effParams.join(',');
    }
    let result_source : string = ""
    try {
	result_source += designs.post;
	result_source += "\n"
	result_source += "\n"
	result_source += "\"use strict\";\n"
	result_source += "var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {\n"
	result_source += "    return new (P || (P = Promise))(function (resolve, reject) {\n"
	result_source += "        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }\n"
	result_source += "        function rejected(value) { try { step(generator[\"throw\"](value)); } catch (e) { reject(e); } }\n"
	result_source += "        function step(result) { result.done ? resolve(result.value) : new P(function (resolve) { resolve(result.value); }).then(fulfilled, rejected); }\n"
	result_source += "        step((generator = generator.apply(thisArg, _arguments || [])).next());\n"
	result_source += "    });\n"
	result_source += "};\n"
	result_source += "Object.defineProperty(exports, \"__esModule\", { value: true });\n"
	result_source += "const openwhisk = require(\"openwhisk\");\n"
	result_source += "const getView = (dbName) => __awaiter(this, void 0, void 0, function* () {\n"
	result_source += "    const ow = openwhisk();\n"
	result_source += "    const entry = yield ow.actions.invoke({\n"
	result_source += "        name: `/whisk.system/cloudant/list-documents`,\n"
	result_source += "        blocking: true,\n"
	result_source += "        params: {\n"
        result_source += "            host: `"+params.cloudant.username+".cloudant.com`,\n"
        result_source += "            username: `"+params.cloudant.username+"`,\n"
        result_source += "            password: `"+params.cloudant.password+"`,\n"
	result_source += "            dbname: dbName,\n"
	result_source += "            params: { include_docs: true }\n"
	result_source += "        }\n"
	result_source += "    });\n"
	result_source += "    const docs = entry.response.result.rows;\n"
	result_source += "    var res = [];\n"
	result_source += "    for (var i = 0; i < docs.length; i++) {\n"
	result_source += "        res.push(docs[i].doc.value);\n"
	result_source += "    }\n"
	result_source += "    return res;\n"
	result_source +=" });\n"
	result_source += "const main = (params) => __awaiter(this, void 0, void 0, function* () {\n"
	result_source += computeEffectiveParams(designs.post_input)+"\n"
	result_source += "   return { \"result\" : db_post("+makeEffectiveParams(designs.post_input)+") }; } );\n"
    } catch (error) {
	return failure("Couldn't create action source string from design document:" + error);
    }

    // Deploy post-processing action to openWhisk
    const ow = openwhisk({"namespace":params.whisk.namespace,
			  "api_key":params.whisk.api_key,
			  "apihost":params.whisk.apihost});
    return ow.packages.update({
	"namespace": params.whisk.namespace,
        "name": "/_/" + pkgname
    }).then(result => {
	ow.actions.update({
	    "namespace": params.whisk.namespace,
            "name" : pkgname + "/result",
            "action" : { "exec" : { "kind" : "nodejs:6" , "code":result_source },
			 "annotations" :[{
			     key: "web-export",
			     value: true
			 }] }
	}).then(r => {
            return failure(`[ACTION] [DEPLOYED] ${JSON.stringify("`+pkgname+`/`+action+`")}`);
	});
    })
}

const failure = (err:string) : Error => {
    return { error: err }
}
