import { Success, Failure, Error, Request, Response} from "./types";
import { Credentials, DeployIn, DeployOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & DeployIn
export type ListOut = { 'success' : string }

const main = async (eparams:Request<ListIn>) : Promise<Response<ListOut>> => {
    // Propagate error
    if ((<Error>eparams).hasOwnProperty('error')) {
	const error: Error = (<Error>eparams);
	return error;
    }

    const params: ListIn = <ListIn>eparams;

    const pkgname: string = params.pkgname;
    const designs: Designs = params.querycode;
    const ow = openwhisk();

    // Get the initial database
    let dbname: string
    try {
	dbname = designs.designs[0].dbname
    } catch (error) {
	console.error("Should have at least one design document")
    }
    // Get the list od documents
    const entries = await ow.actions.invoke({
        name: "/whisk.system/cloudant/list-documents",
        blocking: true,
        params: {
            host: `${params.cloudant.username}.cloudant.com`,
            username: `${params.cloudant.username}`,
            password: `${params.cloudant.password}`,
            dbname: dbname
        }
    })
    // Refresh every record
    const docs = entries.response.result.rows;
    let index = 0;
    function sleep(ms){
	return new Promise(resolve=>{
            setTimeout(resolve,ms)
	})
    }
    await Promise.all(docs.map(async (entry) => {
	index++;
	if (index === 5) { index = 0; await sleep(1000); }
	const entryid = entry.id
        const readResp =
            await ow.actions.invoke({
                name: "/whisk.system/cloudant/read",
                blocking: true,
                params: {
                    host: `${params.cloudant.username}.cloudant.com`,
                    username: `${params.cloudant.username}`,
                    password: `${params.cloudant.password}`,
                    id: entryid,
                    dbname: dbname
                }
            })
	const doc = readResp.response.result
        await ow.actions.invoke({
            name: "/whisk.system/cloudant/update-document",
            blocking: true,
            params: {
                host: `${params.cloudant.username}.cloudant.com`,
                username: `${params.cloudant.username}`,
                password: `${params.cloudant.password}`,
		doc: doc,
                dbname: dbname
            }
        })
	
    }))
    return { "success" : "Deployment successful" };
}

const failure = (statusCode: Failure, err): Response<ListOut> => {
    return { error: { message: err, statusCode: statusCode } }
}
