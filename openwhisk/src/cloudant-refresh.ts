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
    querycode: Designs;
}
export interface ListOut {
    result: any;
}

const main = async (params:ListIn) : Promise<ListIn> => {
    const pkgname: string = params.pkgname;
    const action: string = params.action;
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
    await Promise.all(docs.map(async (entry) => {
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
    return params;
}

const failure = (err) => {
    return { "result": { "error":err } }
}
