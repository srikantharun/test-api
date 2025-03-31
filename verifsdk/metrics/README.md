These files include the definition of cover items.

Each cover item defines the following attributes:
* `name`: Name of the cover item, required to be globally unique. If it's a coverpoint it must as the same name than in the SV file.
* `block`: Block is refers to.
* `category`: type of cover item
    * `HW_COVERGROUP`: regular coverpoint in an SV file
    * `SW_COVERGROUP`: coverpoint sampled by the embedded SW (example: performance targets)
    * `PERFORMANCE`: performance target
    * `ASSERTION`: SV assertion
    * ...
* `description`: 1-3 sentence description of what is covered.
* `owner`: Person responsible for the cover item. First point of contact if it fails or there are any questions.
* `requirement_ids`: Requirement IDs linked to the cover item. ID = prefix_block_category_optional_description_index

