package software.amazon.smithy.dafny.python;

import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CodeInterceptor;
import software.amazon.smithy.python.codegen.sections.SendRequestSection;
import software.amazon.smithy.utils.CodeInterceptor.Appender;

final class SendRequestInterceptor implements
    Appender<SendRequestSection, PythonWriter> {
  @Override
  public Class<SendRequestSection> sectionType() {
    return SendRequestSection.class;
  }

  @Override
  public void append(PythonWriter writer, SendRequestSection section) {
    writer.write("""
                ## HERE
                # Step 7m: Invoke http_client.send
                if config.impl is None:
                    raise Exception("No impl found on the operation config.")
                
                context_with_response = cast(
                    InterceptorContext[Input, None,  GetBooleanInput_GetBooleanInput, GetBooleanOutput_GetBooleanOutput], context
                )
                                
                context_with_response._transport_response = config.impl.GetBoolean(
                    input=context_with_response.transport_request
                )
        """);
  }
}
