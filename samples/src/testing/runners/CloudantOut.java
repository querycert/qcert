package testing.runners;


/** Provides mapping from dbCopy back to viewName+defaultExpr
 */
public class CloudantOut {

	String _dbName;
	String _viewName;
	String _defaultExpr;
        String _dbCopyName;

        CloudantOut() {
	    _dbName=null;
	    _viewName=null;
	    _defaultExpr=null;
	    _dbCopyName=null;
        }
    
        CloudantOut(String dbName, String viewName, String defaultExpr, String dbCopyName) {
		_dbName = dbName;
		_viewName = viewName;
		_defaultExpr = defaultExpr;
		_dbCopyName = dbCopyName;
	}
	
	// Return dbName
	public String getDbName() {
		return _dbName;
	}
	
	// Return viewName
	public String getViewName() {
		return _viewName;
	}
	
	// Return defaultExpr
	public String getDefaultExpr() {
		return _defaultExpr;
	}
	
	// Return dbCopyName
	public String getDbCopyName() {
		return _dbCopyName;
	}

        // Add viewName
        public void addViewName(String viewName) {
	    _viewName = viewName;
	}
    
	// Convert to string
	public String toString() {
	    return "dbCopy [" + _dbCopyName +  "] is mapped to view : [" + _viewName + "] from database [" + _dbName + "]";
	}
	
}
