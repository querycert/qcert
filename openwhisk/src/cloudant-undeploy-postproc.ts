import { Success, Failure, Error, Request, Response} from "./types";
import { Credentials, DeployIn, DeployOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & DeployIn
export type ListOut = Credentials & DeployOut

const main = async (params:ListIn) : Promise<ListOut> => {
    const pkgname: string = params.pkgname;
    const designs: Designs = params.querycode;

    // Delete post-processing action
    const ow = openwhisk({"namespace":params.whisk.namespace,
			  "api_key":params.whisk.api_key,
			  "apihost":params.whisk.apihost});
    return ow.actions.delete({
	"namespace": params.whisk.namespace,
        "name" : pkgname + "/result"
    }).then(r => {
        console.log(`[ACTION] [DELETED] ${JSON.stringify("`+pkgname+`/`+action+`")}`);
    })
}

const failure = (statusCode: Failure, err): Response<ListOut> => {
    return { error: { message: err, statusCode: statusCode } }
}
