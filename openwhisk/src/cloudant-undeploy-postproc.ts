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
    queryname: string;
    querycode: Designs;
}
export interface ListOut {
    result: any;
}

const main = async (params:ListIn) : Promise<ListOut> => {
    const pkgname: string = params.pkgname;
    const queryname: string = params.queryname;
    const designs: Designs = params.querycode;

    // Delete post-processing action
    const ow = openwhisk({"namespace":params.whisk.namespace,
			  "api_key":params.whisk.api_key,
			  "apihost":params.whisk.apihost});
    return ow.actions.delete({
	"namespace": params.whisk.namespace,
        "name" : pkgname + "/" + queryname
    }).then(r => {
        console.log(`[ACTION] [DELETED] ${JSON.stringify("`+pkgname+`/`+queryname+`")}`);
    })
}

const failure = (err) => {
    return { error: err }
}
