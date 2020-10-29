module Result = struct
 type 'a t =
   | WellTyped of 'a
   | IllTyped
   | ImplementationBug
end
