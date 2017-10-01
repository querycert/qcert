export interface Credentials {
    cloudant: {
        username: string;    /** Cloudant username for the service */
        password: string;    /** Cloudant password for the service */
    }
    whisk: {
        namespace: string;   /** openWhisk namespace for the service */
        api_key: string;     /** openWhisk key for the service */
        apihost: string;     /** openWhisk host for the service */
    }
}

export interface Design {
    dbname: string;          /** Cloudant database name */
    design: { views: any; }; /** Cloudant view */
}

export interface Designs {
    designs: Design[];       /** Design documents */
    post: string;            /** Post-processing expression */
    post_input: string[];    /** Effective parameters for the post-processing expression */
}

export interface Error { error: string; }
export type Request<T> = T | Error
export type Response<T> = T | Error

export interface CompileIn {
    pkgname: string;
    query: string;
    schema: string;
    source: string;
}
export interface CompileOut {
    pkgname: string;
    querycode:Designs;
}
export type DeployIn = CompileOut
export type DeployOut = DeployIn
