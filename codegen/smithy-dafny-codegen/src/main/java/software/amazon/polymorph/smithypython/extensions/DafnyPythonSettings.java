package software.amazon.polymorph.smithypython.extensions;

import software.amazon.polymorph.smithypython.Constants.GenerationType;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.python.codegen.PythonSettings;

public class DafnyPythonSettings extends PythonSettings {

  private GenerationType generationType;

  public static DafnyPythonSettings from(ObjectNode config) {
    PythonSettings pythonSettings = PythonSettings.from(config);
    DafnyPythonSettings dafnyPythonSettings = new DafnyPythonSettings();
    dafnyPythonSettings.setModuleDescription(pythonSettings.getModuleDescription());
    dafnyPythonSettings.setModuleVersion(pythonSettings.getModuleVersion());
    dafnyPythonSettings.setService(pythonSettings.getService());
    dafnyPythonSettings.setModuleName(pythonSettings.getModuleName());
    return dafnyPythonSettings;
  }

  public void setGenerationType(GenerationType generationType) {
    this.generationType = generationType;
  }

  public GenerationType getGenerationType() {
    return generationType;
  }

}
