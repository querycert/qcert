import { Config, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = {
    whisk: {
	namespace: string;
	api_key: string;
	apihost: string;
    };
    cloudant: {
	username: string;
	password: string;
    }
    pkgname: string;
    action: string;
    query: string;
    schema: string;
    source: string;
}
export interface ListOut {
    whisk: {
	namespace: string;
	api_key: string;
	apihost: string;
    };
    cloudant: {
	username: string;
	password: string;
    }
    pkgname: string;
    action: string;
    querycode: Designs;
}

const main = async (params:ListIn) : Promise<ListOut> => {
    const whisk = params.whisk;
    const cloudant = params.cloudant;
    const source: string = params.source;
    const pkgname: string = params.pkgname;
    const action: string = params.action;
    const querytext: string = params.query;
    const schema: string = JSON.stringify(params.schema);

    const ow = openwhisk()

    // Deploy post-processing action to openWhisk
    let compiled
    try {
	compiled = await ow.actions.invoke({
	    name: "qcert/compile",
	    blocking: true,
	    params: {
		source: source,
		target: 'cloudant',
		query: querytext,
		schema: schema
	    }
	});
    } catch (err) {
	console.log('Compilation error for query: "'+querytext+'" with error'+err);
    }
    return {
	whisk: whisk,
	cloudant: cloudant,
	pkgname: pkgname,
	action: action,
	querycode: JSON.parse(compiled.response.result.result)
    };
}

const failure = (err) => {
    return { result : { error: err } }
}
