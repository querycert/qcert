/*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package testing.runners;

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.util.logging.Logger;

/**
 * A generic process launcher
 */
public class BasicLauncher extends Launcher {

  protected String cmd;

  public BasicLauncher(boolean captureOutput, boolean captureErr, Logger logger) {
    super(captureOutput, captureErr, logger);
  }

  public String getCmd() {
    return cmd;
  }

  public void setCmd(String newCmd) {
    cmd = newCmd;
  }

  @Override
  public String toString() {
    StringBuffer result = new StringBuffer(super.toString());
    result.append(" (cmd: ");
    result.append(cmd);
    return result.toString();
  }

  /**
   * Launch the process and wait until it is finished.  Returns the exit value of the process.
   */
  public int launch() throws  IllegalArgumentException, IOException {
    Process p = spawnProcess(getCmd());
    Thread d1 = isCaptureErr() ? captureStdErr(p) : drainStdErr(p);
    Thread d2 = isCaptureOutput() ? captureStdOut(p) : drainStdOut(p);
    if (getInput() != null) {
      final BufferedOutputStream input = new BufferedOutputStream(p.getOutputStream());
      try {
        input.write(getInput(), 0, getInput().length);
        input.flush();
        input.close();
      } catch (IOException e) {
        e.printStackTrace();
        throw new IOException("error priming stdin", e);
      }
    }
    try {
      d1.join();
      d2.join();
    } catch (InterruptedException e) {
      throw new Error("Internal error", e);
    }
    if (isCaptureErr()) {
      Drainer d = (Drainer) d1;
      setStdErr(d.getCapture().toByteArray());
    }
    if (isCaptureOutput()) {
      Drainer d = (Drainer) d2;
      setStdOut(d.getCapture().toByteArray());
    }
    return p.exitValue();
  }
}
