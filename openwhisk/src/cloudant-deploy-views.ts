import { Success, Failure, Error, Request, Response} from "./types";
import { Credentials, DeployIn, DeployOut, Design, Designs } from "./types";
import openwhisk = require("openwhisk");

export type ListIn = Credentials & DeployIn
export type ListOut = Credentials & DeployOut

const main = async (eparams:Request<ListIn>) : Promise<Response<ListIn>> => {
    // Propagate error
    if ((<Error>eparams).hasOwnProperty('error')) {
	const error: Error = (<Error>eparams);
	return error;
    }

    const params: ListIn = <ListIn>eparams;
    
    const pkgname: string = params.pkgname;
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
		return failure(500,'Unable to create database:'+dbname+' with error:'+err);
            }
	}))
	
	const viewname = '"_design/'+pkgname+'"'
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
            return failure(500,'Unable to create view in database:'+dbname+' with error:'+err)
        }
	console.log('CREATED VIEW IN:'+dbname)
    }))
    return params;
}

const failure = (statusCode: Failure, err): Response<ListOut> => {
    return { error: { message: err, statusCode: statusCode } }
}
