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
    const ow = openwhisk()

    // Load Cloudant Views
    const res = await Promise.all(designs.designs.map(async (design:Design) => {
	const dbname: string = design.dbname
	const views = design.design.views
	var dbcopies = []
	for (var key in views) {
	    if (views.hasOwnProperty(key)) {
		dbcopies.push(views[key].dbcopy);
	    }
	}
	
	const dbcopy = views.dbcopy
	await Promise.all(dbcopies.map(async (dbcopy) => {
            try {
		await ow.actions.invoke({
		    name: "/whisk.system/cloudant/create-database",
		    blocking: true,
		    params: {
			host: `${params.cloudant.username}.cloudant.com`,
			username: `${params.cloudant.username}`,
			password: `${params.cloudant.password}`,
			dbname: dbcopy
		    }
		})
            } catch (err) {
		console.log('Unable to create database:'+dbname+' with error:'+err);
            }
	}))
	
	const viewname = '"_design/'+queryname+'"'
        try {
            await ow.actions.invoke({
		name: "/whisk.system/cloudant/create-document",
		blocking: true,
		params: {
                    host: `${params.cloudant.username}.cloudant.com`,
                    username: `${params.cloudant.username}`,
                    password: `${params.cloudant.password}`,
                    dbname: dbname,
		    doc: {"views":views},
		    params: viewname
		}
            })
        } catch (err) {
            console.log('Unable to create view in database:'+dbname+' with error:'+err)
        }
	return failure('ACTUALLY CREATED VIEW IN:'+dbname)
    }))
    return { "result" : res };
}

const failure = (err) => {
    return { error: err }
}
