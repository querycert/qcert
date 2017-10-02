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
    
    let undeploy_source : string = ""
    try {
	undeploy_source += "\"use strict\";\n"
	undeploy_source += "var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {\n"
	undeploy_source += "    return new (P || (P = Promise))(function (resolve, reject) {\n"
	undeploy_source += "        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }\n"
	undeploy_source += "        function rejected(value) { try { step(generator[\"throw\"](value)); } catch (e) { reject(e); } }\n"
	undeploy_source += "        function step(result) { result.done ? resolve(result.value) : new P(function (resolve) { resolve(result.value); }).then(fulfilled, rejected); }\n"
	undeploy_source += "        step((generator = generator.apply(thisArg, _arguments || [])).next());\n"
	undeploy_source += "    });\n"
	undeploy_source += "};\n"
	undeploy_source += "Object.defineProperty(exports, \"__esModule\", { value: true });\n"
	undeploy_source += "const openwhisk = require(\"openwhisk\");\n"
	undeploy_source += "const main = (eparams) => __awaiter(this, void 0, void 0, function* () {\n"
	undeploy_source += "const params = " + JSON.stringify(params) + ";\n\n"
	undeploy_source += "    const pkgname = params.pkgname;\n"
	undeploy_source += "    const designs = params.querycode;\n"
	undeploy_source += "    const ow = openwhisk();\n"
	undeploy_source += "    // Delete dbcopies\n"
	undeploy_source += "    yield Promise.all(designs.designs.map((design) => __awaiter(this, void 0, void 0, function* () {\n"
	undeploy_source += "        const dbname = design.dbname;\n"
	undeploy_source += "        const views = design.design.views;\n"
	undeploy_source += "        var dbcopies = [];\n"
	undeploy_source += "        for (var key in views) {\n"
	undeploy_source += "            if (views.hasOwnProperty(key)) {\n"
	undeploy_source += "                dbcopies.push(views[key].dbcopy);\n"
	undeploy_source += "            }\n"
	undeploy_source += "        }\n"
	undeploy_source += "        const dbcopy = views.dbcopy;\n"
	undeploy_source += "        yield Promise.all(dbcopies.map((dbcopy) => __awaiter(this, void 0, void 0, function* () {\n"
	undeploy_source += "            try {\n"
	undeploy_source += "                yield ow.actions.invoke({\n"
	undeploy_source += "                    name: \"/whisk.system/cloudant/delete-database\",\n"
	undeploy_source += "                    blocking: true,\n"
	undeploy_source += "                    params: {\n"
	undeploy_source += "                        host: `${params.cloudant.username}.cloudant.com`,\n"
	undeploy_source += "                        username: `${params.cloudant.username}`,\n"
	undeploy_source += "                        password: `${params.cloudant.password}`,\n"
	undeploy_source += "                        dbname: dbcopy\n"
	undeploy_source += "                    }\n"
	undeploy_source += "                });\n"
	undeploy_source += "            }\n"
	undeploy_source += "            catch (err) {\n"
	undeploy_source += "                console.log('Unable to delete database:' + dbname + ' with error:' + err);\n"
	undeploy_source += "            }\n"
	undeploy_source += "        })));\n"
	undeploy_source += "    })));\n"
	undeploy_source += "\n"
	undeploy_source += "    // Delete initial database view\n"
	undeploy_source += "    let firstDesign;\n"
	undeploy_source += "    try {\n"
	undeploy_source += "        firstDesign = designs.designs[0];\n"
	undeploy_source += "    }\n"
	undeploy_source += "    catch (error) {\n"
	undeploy_source += "        console.error(\"Should have at least one design document\");\n"
	undeploy_source += "    }\n"
	undeploy_source += "    const viewname = '_design/' + pkgname;\n"
	undeploy_source += "    try {\n"
	undeploy_source += "        const entry = yield ow.actions.invoke({\n"
	undeploy_source += "            name: \"/whisk.system/cloudant/read\",\n"
	undeploy_source += "            blocking: true,\n"
	undeploy_source += "            params: {\n"
	undeploy_source += "                host: `${params.cloudant.username}.cloudant.com`,\n"
	undeploy_source += "                username: `${params.cloudant.username}`,\n"
	undeploy_source += "                password: `${params.cloudant.password}`,\n"
	undeploy_source += "                docid: viewname,\n"
	undeploy_source += "                dbname: firstDesign.dbname\n"
	undeploy_source += "            }\n"
	undeploy_source += "        });\n"
	undeploy_source += "        yield ow.actions.invoke({\n"
	undeploy_source += "            name: \"/whisk.system/cloudant/delete-document\",\n"
	undeploy_source += "            blocking: true,\n"
	undeploy_source += "            params: {\n"
	undeploy_source += "                host: `${params.cloudant.username}.cloudant.com`,\n"
	undeploy_source += "                username: `${params.cloudant.username}`,\n"
	undeploy_source += "                password: `${params.cloudant.password}`,\n"
	undeploy_source += "                docid: viewname, docrev: entry.response.result._rev,\n"
	undeploy_source += "                dbname: firstDesign.dbname\n"
	undeploy_source += "            }\n"
	undeploy_source += "        });\n"
	undeploy_source += "    }\n"
	undeploy_source += "    catch (err) {\n"
	undeploy_source += "        console.log('Unable to delete view ' + viewname + ' in database:' + firstDesign.dbname + ' with error:' + err);\n"
	undeploy_source += "    }\n"
	undeploy_source += "    // Delete post-processing action\n"
	undeploy_source += "    return ow.actions.delete({\n"
	undeploy_source += "        \"name\": pkgname + \"/result\"\n"
	undeploy_source += "    }).then(r => {\n"
	undeploy_source += "        console.log(`[ACTION] [DELETED] ${JSON.stringify(\"`+pkgname+`/result\")}`);\n"
	undeploy_source += "        // Delete undeploy action\n"
	undeploy_source += "        ow.actions.delete({\n"
	undeploy_source += "            \"name\": pkgname + \"/undeploy\"\n"
	undeploy_source += "        }).then(r => {\n"
	undeploy_source += "            console.log(`[ACTION] [DELETED] ${JSON.stringify(\"`+pkgname+`/undeploy\")}`);\n"
	undeploy_source += "            // Delete query package\n"
	undeploy_source += "            ow.packages.delete({\n"
	undeploy_source += "                \"name\": \"/_/\" + pkgname\n"
	undeploy_source += "            }).then(r => {\n"
	undeploy_source += "                console.log(`[PACKAGE] [DELETED] ${JSON.stringify(\"/_/`+pkgname+`\")}`);\n"
	undeploy_source += "            });\n"
	undeploy_source += "        });\n"
	undeploy_source += "    });\n"
	undeploy_source += "});\n"
	undeploy_source += "const failure = (err) => {\n"
	undeploy_source += "    return { error: err };\n"
	undeploy_source += "};\n"
    } catch (error) {
	return failure("Couldn't create undeploy action source string from design document:" + error);
    }

    // Deploy post-processing action to openWhisk
    const ow = openwhisk({"namespace":params.whisk.namespace,
			  "api_key":params.whisk.api_key,
			  "apihost":params.whisk.apihost});
   return ow.packages.update({
	"namespace": params.whisk.namespace,
        "name": "/_/" + params.pkgname
    }).then(result => {
	ow.actions.update({
	    "namespace": params.whisk.namespace,
            "name" : params.pkgname + "/undeploy",
            "action" : { "exec" : { "kind" : "nodejs:6" , "code":undeploy_source } }
	}).then(r => {
            return failure(`[ACTION] [DEPLOYED] ${JSON.stringify("`+params.pkgname+`/undeploy")}`);
	});
	return eparams;
    })
}

const failure = (err:string) : Error => {
    return { error: err }
}
