import { Success, Failure, Error, Request, Response} from "./types";
import { Credentials, CompileIn, CompileOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & CompileIn
export type ListOut = Credentials & CompileOut & { statusCode: Success }

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
	const schema: string = JSON.stringify(params.schema);

	const ow = openwhisk()
	// Call compiler action for cloudant
	const compiled = await ow.actions.invoke({
	    name: "qcert/compile",
	    blocking: true,
	    params: {
		qname: pkgname,
		source: source,
		target: 'cloudant',
		query: querytext,
		schema: schema
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

