package software.amazon.polymorph.smithygo.codegen;

import software.amazon.polymorph.smithygo.LocalServiceGenerator;
import software.amazon.smithy.model.shapes.ServiceShape;

public class ClientGenerator implements Runnable {
    private final GenerationContext context;
    private final ServiceShape service;

    ClientGenerator(GenerationContext context, ServiceShape service) {
        this.context = context;
        this.service = service;
    }

    @Override
    public void run() {
       new LocalServiceGenerator(context, service).run();
    }
}
