import { Success, Failure, Error, Request, Response} from "./types";
import { Credentials, CompileIn, CompileOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & CompileIn
export type ListOut = Credentials & CompileOut & { statusCode: Success }

const constructSchema = (dbs:string[]) => {
    let globals = {}
    for (var i = 0; i < dbs.length; i++) {
	const db = dbs[i];
	globals[db] = { "dist" : "distr",
			"type" : { "$coll" : "Top" } };
    }
    return { "hierarchy": [],
	     "brandTypes" :[],
	     "typeDefs" :[],
	     "globals" : globals };
}

const main = async (params:ListIn) : Promise<Response<ListOut>> => {
    try {
	const whisk = params.whisk;
	const cloudant = params.cloudant;
	const source: string = params.source;
	let pkgname : string
	if (params.hasOwnProperty('pkgname')) {
	    if (params.pkgname === '') { return failure(400,"A package name must be provided") }
	    pkgname = params.pkgname;
	}
	else { return failure(400,"A package name must be provided") }
	const querytext: string = params.query;

	const ow = openwhisk()

	// Guess the schema from Cloudant, if it isn't given
	let schema
	if (params.hasOwnProperty('schema')) {
	    schema = params.schema;
	} else {
	    const entries = await ow.actions.invoke({
		name: "/whisk.system/cloudant/list-all-databases",
		blocking: true,
		params: {
		    host: `${params.cloudant.username}.cloudant.com`,
		    username: `${params.cloudant.username}`,
		    password: `${params.cloudant.password}`
		}
	    });
	    const dbnames = entries.response.result.all_databases;
	    schema = constructSchema(dbnames);
	}
	
	// Call compiler action for cloudant
	const compiled = await ow.actions.invoke({
	    name: "qcert/compile",
	    blocking: true,
	    params: {
		qname: pkgname,
		source: source,
		target: 'cloudant',
		query: querytext,
		schema: JSON.stringify(schema)
	    }
	});
	return {
	    whisk: whisk,
	    cloudant: cloudant,
	    pkgname: pkgname,
	    querycode: JSON.parse(compiled.response.result.result),
	    statusCode: 200
	};
    } catch (err) {
	return failure(500,'Compilation error: '+err);
    }
}

const failure = (statusCode: Failure, err): Response<ListOut> => {
    return { error: { message: err, statusCode: statusCode } }
}

