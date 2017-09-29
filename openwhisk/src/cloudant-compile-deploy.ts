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
    source: string;
}
export interface ListOut {
    result: any;
}

const main = async (params:ListIn) : Promise<ListOut> => {
    const whiskcred = params.whisk;
    const cloudantcred = params.cloudant;
    const source: string = params.source;
    const pkgname: string = params.pkgname;
    const action: string = params.action;
    const querytext: string = params.query;

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
	    }
	});
    } catch (err) {
	return failure('Compilation error for query: "'+querytext+'" with error'+err);
    }
    try {
	const deployload = {
	    whisk: whiskcred,
	    cloudant: cloudantcred,
	    pkgname: pkgname,
	    action: action,
	    querycode: JSON.parse(compiled.response.result.result)
	};
	const deployed = await ow.actions.invoke({
	    name: "qcert/cloudant-deploy",
	    blocking: true,
	    params: deployload
	});
    } catch (err) {
	return failure('Deployment error for query: "'+querytext+'" with error'+err);
    }
    return { result : { success: "Compiled query"+querytext } }
}

const failure = (err) => {
    return { result : { error: err } }
}
