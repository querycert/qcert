import { Error, Request, Response, Credentials, CompileIn, CompileOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & CompileIn
export type ListOut = Credentials & CompileOut

const main = async (params:ListIn) : Promise<Response<ListOut>> => {
    const whisk = params.whisk;
    const cloudant = params.cloudant;
    const source: string = params.source;
    const pkgname: string = params.pkgname;
    const querytext: string = params.query;
    const schema: string = JSON.stringify(params.schema);

    const ow = openwhisk()
    // Call compiler action for cloudant
    let compiled
    try {
	compiled = await ow.actions.invoke({
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
    } catch (err) {
	return failure('Compilation error for query: "'+querytext+'" with error'+err);
    }
    return {
	whisk: whisk,
	cloudant: cloudant,
	pkgname: pkgname,
	querycode: JSON.parse(compiled.response.result.result)
    };
}

const failure = (err:string) : Error => {
    return { error: err }
}
